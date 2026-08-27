//! Python bindings for Leo3 — safe, ergonomic Rust bindings for the Lean4
//! theorem prover.
//!
//! This is the native extension module `leotower._leotower`.  The ergonomic
//! Python-facing surface lives in `python/leotower/__init__.py`.

use leo3::ffi;
use leo3::prelude::*;
use pyo3::exceptions::PyRuntimeError;
use pyo3::prelude::*;
use std::mem::ManuallyDrop;

/// Convert a leo3 `LeanResult` error into a Python `RuntimeError`.
fn to_py_err(e: impl std::fmt::Display) -> PyErr {
    PyRuntimeError::new_err(e.to_string())
}

/// Error text for an out-of-range replay-state id, including the valid
/// range so users can self-correct.
fn unknown_state_msg(state: u64, len: usize) -> String {
    if len == 0 {
        format!("unknown state {state} (no states yet; call set_goal first)")
    } else {
        format!("unknown state {state} (valid states: 0..={})", len - 1)
    }
}

/// Initialize the Lean runtime eagerly (one-time worker-thread bootstrap).
///
/// Idempotent; `with_lean()` also ensures initialization on first use.
#[pyfunction]
fn prepare_freethreaded_lean() {
    leo3::prepare_freethreaded_lean();
}

/// A session into the shared Lean runtime.
///
/// Obtained from `leotower.with_lean()`.  Each method runs on the calling
/// thread, which is safely attached to Lean's runtime on first use; the
/// session itself holds no Lean-owned state.
#[pyclass]
struct LeanSession {
    _private: (),
}

#[pymethods]
impl LeanSession {
    /// Construct a session (no Lean state is created until the first
    /// operation; `with_lean()` additionally ensures runtime bootstrap).
    #[new]
    fn new() -> Self {
        LeanSession { _private: () }
    }

    /// Round-trip a `u64` through Lean's `Nat` runtime object.
    fn nat_roundtrip(&self, n: u64) -> PyResult<u64> {
        leo3::with_lean(|lean| -> LeanResult<_> {
            let nat = LeanNat::from_usize(lean, n as usize)?;
            Ok(LeanNat::to_usize(&nat)? as u64)
        })
        .map_err(to_py_err)
    }

    /// Add two `u64`s with Lean's runtime `Nat.add` (real Lean computation,
    /// including the big-nat path).
    fn nat_add(&self, a: u64, b: u64) -> PyResult<u64> {
        leo3::with_lean(|lean| -> LeanResult<_> {
            let x = LeanNat::from_usize(lean, a as usize)?;
            let y = LeanNat::from_usize(lean, b as usize)?;
            let sum = LeanNat::add(x, y)?;
            Ok(LeanNat::to_usize(&sum)? as u64)
        })
        .map_err(to_py_err)
    }

    /// `a ^ b` computed by Lean's runtime `Nat.pow`, returned as a decimal
    /// string (exact beyond `u64` range).
    fn pow_str(&self, a: u64, b: u64) -> PyResult<String> {
        leo3::with_lean(|lean| -> LeanResult<_> {
            let base = LeanNat::from_usize(lean, a as usize)?;
            let exp = LeanNat::from_usize(lean, b as usize)?;
            let power = LeanNat::pow(base, exp)?;
            Ok(LeanNat::repr(&power))
        })
        .map_err(to_py_err)
    }

    /// Round-trip a `str` through Lean's `String` runtime object (embedded
    /// NUL bytes survive the round trip).
    fn string_roundtrip(&self, s: &str) -> PyResult<String> {
        leo3::with_lean(|lean| -> LeanResult<_> {
            let obj = LeanString::mk(lean, s)?;
            Ok(LeanString::cstr(&obj)?.to_owned())
        })
        .map_err(to_py_err)
    }
}

// ============================================================================
// Repl — LeanDojo-compatible replay layer
// ============================================================================

use leo3::instance::LeanAny;
use leo3::meta::context::{CoreContext, CoreState, MetaContext, MetaState};
use leo3::meta::environment::{ConstantKind, LeanConstantInfo, LeanEnvironment};
use leo3::meta::expr::LeanExpr;
use leo3::meta::metam::MetaMContext;
use leo3::meta::name::LeanName;
use leo3::meta::repl::{import_modules_with_exts, pp_exprs, run_tactic};
use leo3::unbound::LeanUnbound;

/// One replay state: the remaining goals (metavariable IDs) and a snapshot
/// of the `Meta.State` at that point. Each `run_tac` rebuilds the `ST.Ref`
/// from the *target state's* snapshot, so branching stays independent.
struct ReplState {
    goals: Vec<LeanUnbound<LeanName>>,
    meta_state: LeanUnbound<LeanAny>,
}

/// An environment reference that releases its compacted import regions when
/// the owning [`Repl`] is dropped (W-407 Bug A — per-`Repl` leak of
/// ~1.4–1.6 GB).
///
/// `import_modules_with_exts` compacts each module's olean payload into C++
/// `compacted_region` buffers attached to the environment header. The
/// reference-counted drop path (`lean_dec`) never frees those buffers — only
/// `Environment.freeRegions` does, and the stock runtime only invokes it from
/// the one-shot `lean` CLI path. Without this release, every `Repl()`
/// permanently leaks one ~1.4–1.6 GB buffer.
///
/// The inner `ManuallyDrop` makes this type's `Drop` the only place the
/// environment's reference count is released: it hands the raw pointer to
/// `free_regions` (which `dec`s once and frees the regions). It also lets
/// [`Self::swap_inner`] replace the environment in place (used by
/// [`Repl::save`]) without triggering a region free.
///
/// **This must remain the last field of [`Repl`].** With no custom `Drop` on
/// [`Repl`], Rust drops struct fields in declaration order, so the
/// environment outlives every object derived from its import (the four
/// Core/Meta parts and the replay states) — exactly `free_regions`' safety
/// precondition.
struct EnvRegions {
    env: ManuallyDrop<LeanUnbound<LeanEnvironment>>,
    /// Top-level module names imported into this environment, kept for the
    /// W-417 keepalive (see [`Drop for EnvRegions`]).
    modules: Vec<String>,
    /// Number of lean file VMAs this environment's import added (the import
    /// time `/proc/self/maps` diff). Compared against the live region count at
    /// drop time to decide whether *every* region is file-backed and therefore
    /// safe to `free_regions` (see [`Drop for EnvRegions`]).
    file_vmas_added: u64,
    /// The lean file VMAs this environment's import added (the import-time
    /// `/proc/self/maps` range diff). On a safe free, the set recorded for a
    /// later cross-set re-map is diffed against a post-free snapshot from *this*
    /// per-environment set — never a process-wide snapshot, which would conflate
    /// a second environment's live regions into this one's record (W-417).
    imported_vmras: Vec<leo3::meta::LeanVma>,
    /// True while the file-backed count computed at import time is trustworthy.
    /// False when the import window showed identity churn on a pre-existing
    /// mapping (its backing file modified/unlinked/recreated) — then
    /// `file_vmas_added` is unreliable and the drop gate leaks instead of
    /// risking a free of a heap-mixed environment.
    trackable: bool,
}

impl EnvRegions {
    fn new(
        env: LeanUnbound<LeanEnvironment>,
        modules: Vec<String>,
        file_vmas_added: u64,
        imported_vmras: Vec<leo3::meta::LeanVma>,
        trackable: bool,
    ) -> Self {
        Self {
            env: ManuallyDrop::new(env),
            modules,
            file_vmas_added,
            imported_vmras,
            trackable,
        }
    }

    /// Replace the inner environment in place, returning the old one. Does
    /// **not** free the old environment's regions: the replacement shares the
    /// old environment's region buffers (environments grow in place), so the
    /// caller must release the old environment with a plain `lean_dec` (see
    /// [`Repl::save`]).
    fn swap_inner(
        &mut self,
        new_env: LeanUnbound<LeanEnvironment>,
    ) -> LeanUnbound<LeanEnvironment> {
        let mut old_md = std::mem::replace(&mut self.env, ManuallyDrop::new(new_env));
        // The replacement environment shares the old environment's region
        // buffers (Lean environments grow in place), so the file-backed-ness
        // computed at import time is still valid: `free_regions` at drop time
        // releases the same import regions. Do NOT mark untrackable here —
        // doing so leaked the env after every `set_goal`/`run_tac`/`run_cmd`
        // and re-introduced the W-407 region leak.
        unsafe { ManuallyDrop::take(&mut old_md) }
    }
}

impl std::ops::Deref for EnvRegions {
    type Target = LeanUnbound<LeanEnvironment>;
    fn deref(&self) -> &Self::Target {
        &self.env
    }
}

impl Drop for EnvRegions {
    fn drop(&mut self) {
        #[cfg(target_os = "linux")]
        {
            // W-417 stopgap: decide whether this environment's regions are safe
            // to free by proving *per region* that every compacted region is
            // file-backed (a re-mappable VMA), not by a stale set-level flag.
            //
            // `free_regions` releases every region, including any **heap**
            // region (the `malloc` buffer the Lean `module.cpp` fallback uses
            // when a deterministic `mmap` base is already occupied). A heap
            // region's `g_native_symbol_cache` keys point into that buffer and
            // cannot be re-mapped once freed, so freeing a heap/mixed
            // environment dangles them and the next import's symbol lookup
            // SIGSEGVs.
            //
            // An environment is all-file-backed exactly when its live region
            // count equals the number of lean file VMAs its import added (each
            // file-backed region is one `mmap`; a heap region adds none). Any
            // uncertainty — the count unreadable, a mismatch, or an untracked
            // (`Repl::save`-swapped) environment — leaks instead.
            let modules: Vec<&str> = self.modules.iter().map(|s| s.as_str()).collect();
            // Serialize the whole free/record sequence against the
            // remap/import sequences (their `/proc/self/maps` snapshots and
            // record steps run on caller threads and would otherwise interleave
            // with this free and corrupt the freed-set record).
            let _lifecycle = leo3::meta::lifecycle_lock();
            // Quarantined: a prior destructive free failed in a way that could
            // not be proven fully recovered. Do not free (it could create more
            // dangling keys that no re-map would revive); leak instead.
            if leo3::meta::keepalive_poisoned() {
                eprintln!("leotower: keepalive is quarantined; leaking env instead of freeing");
                let _ = unsafe { ManuallyDrop::take(&mut self.env) };
                return;
            }
            // `self.env` is a live environment this `EnvRegions` owns (the last
            // live reference). `environment_region_count` is `unsafe`: it walks
            // the pinned `Environment` layout, and the type cannot prove the
            // object is a real environment (`LeanUnbound::cast` can forge one).
            // The contract holds: `self.env` is a genuine, live environment.
            let region_count = unsafe { leo3::meta::environment_region_count(&self.env) };
            let should_free = self.trackable
                && leo3::meta::safe_to_free_regions(region_count, self.file_vmas_added);
            if !should_free {
                // Leak: releasing without `free_regions` never dangles a key.
                let _ = unsafe { ManuallyDrop::take(&mut self.env) };
                return;
            }
            // This env's file-backed regions, captured at import time (range
            // diff). The dropped set is recorded from THIS per-env set — never a
            // process-wide snapshot, which would conflate a second
            // environment's live regions into this one's record (W-417).
            let imported = self.imported_vmras.clone();
            // An untrackable region (its import-time `stat` failed, or it was
            // deleted) cannot have its identity re-verified on re-map, so
            // freeing it would leave an unrecoverable dangling key. Leak the
            // whole env rather than free it.
            if imported.iter().any(|v| !v.size_known) {
                eprintln!(
                    "leotower: an import region was not trackable at snapshot time; leaking env instead of freeing"
                );
                let _ = unsafe { ManuallyDrop::take(&mut self.env) };
                return;
            }
            let unbound = unsafe { ManuallyDrop::take(&mut self.env) };
            let env_ptr = unbound.into_ptr();
            // All regions verified file-backed and trackable: free, then record
            // the regions `free_regions` unmapped for a later cross-set import
            // to re-map (reviving dangling cache keys).
            let free_result = leo3::with_lean(|lean| {
                let bound = unsafe { LeanBound::from_owned_ptr(lean, env_ptr) };
                unsafe { bound.free_regions() }
            });
            // `free_regions` is a *non-atomic* `forM CompactedRegion.free`: an
            // error can occur after the first regions are already unmapped,
            // leaving them dangling. Never leave that unrecorded — the next
            // cross-set import would dereference the dangling keys. Recover
            // what we can; when we cannot, quarantine the process.
            let after = leo3::meta::snapshot_lean_vmras();
            match &free_result {
                Err(e) => match &after {
                    // Post-state readable: record exactly what was unmapped.
                    Ok(a) => {
                        let freed = leo3::meta::diff_freed_vmras(&imported, a);
                        let n = freed.len();
                        leo3::meta::record_freed_set(&modules, freed);
                        eprintln!(
                            "leotower: free_regions failed during drop ({e}); recovered \
                             {} freed region(s) so a later cross-set import revives them",
                            n
                        );
                    }
                    // Post-state unreadable too: we cannot determine the freed
                    // set. Quarantine — no further destructive free (future
                    // drops leak) and no further import (the re-map blocks), so
                    // the dangling keys can never be dereferenced.
                    Err(e2) => {
                        leo3::meta::poison_keepalive();
                        eprintln!(
                            "leotower: free_regions failed ({e}) AND /proc/self/maps unreadable \
                             ({e2}) during drop; CANNOT determine freed regions -> keepalive \
                             QUARANTINED (future envs leak, imports blocked)"
                        );
                    }
                },
                Ok(()) => match &after {
                    // Normal path: the free succeeded; record precisely what it
                    // unmapped.
                    Ok(a) => {
                        let freed = leo3::meta::diff_freed_vmras(&imported, a);
                        leo3::meta::record_freed_set(&modules, freed);
                    }
                    // Free succeeded but post-state unreadable: every region of
                    // this env was unmapped. `imported` is exactly this env's
                    // regions (precise, per-env), so record it for a best-effort
                    // revive (a later cross-set import re-maps it; an occupied
                    // address just fails the no-clobber remap).
                    Err(e) => {
                        leo3::meta::record_freed_set(&modules, imported.clone());
                        eprintln!(
                            "leotower: free_regions succeeded but /proc/self/maps unreadable \
                             ({e}); recording the pre-free VMA set as a best-effort revive"
                        );
                    }
                },
            }
        }
        #[cfg(not(target_os = "linux"))]
        {
            // The keepalive stopgap is Linux-only (it reads /proc/self/maps and
            // relies on MAP_FIXED_NOREPLACE). On other platforms we release the
            // environment with a plain `lean_dec`, leaking the compacted import
            // regions (the W-407 cost) but — crucially — NOT calling
            // `free_regions`, which would dangle the global symbol-cache keys
            // and crash the next cross-set import.
            let _ = unsafe { ManuallyDrop::take(&mut self.env) };
        }
    }
}

/// W-417 stopgap: re-map the freed cross-set lean regions before a cross-set
/// import, and **block the import** if any region cannot be safely re-mapped —
/// proceeding would risk the original dangling-key SIGSEGV. The stopgap is
/// Linux-only, so this is a no-op on other platforms.
#[cfg(target_os = "linux")]
fn block_on_remap(importing: &[&str]) -> LeanResult<()> {
    leo3::meta::remap_cross_set_bases(importing).map_err(|errs| {
        LeanError::other(&format!(
            "cannot revive freed import regions before importing {importing:?}: {}",
            errs.iter()
                .map(std::string::ToString::to_string)
                .collect::<Vec<_>>()
                .join("; ")
        ))
    })
}

#[cfg(not(target_os = "linux"))]
fn block_on_remap(_importing: &[&str]) -> LeanResult<()> {
    Ok(())
}

/// A LeanDojo-style replay session over the embedded Lean runtime.
///
/// State 0 is the root: after `set_goal` it holds the initial goal. Each
/// `run_tac` appends a new state; `get_goals(state)` / `get_num_goals(state)`
/// / `get_goal_pp(state)` inspect it. Invalid tactics raise `RuntimeError`
/// instead of crashing the interpreter.
#[pyclass]
pub struct Repl {
    core_ctx: LeanUnbound<CoreContext>,
    core_state: LeanUnbound<CoreState>,
    /// Monotonic counter for the `have`-declaration names used by
    /// [`Self::check`] (guarantees a fresh name per call).
    check_counter: u64,
    meta_ctx: LeanUnbound<MetaContext>,
    meta_state: LeanUnbound<MetaState>,
    states: Vec<ReplState>,
    /// The imported environment; released (compacted import regions freed) by
    /// [`EnvRegions::drop`] when the `Repl` is destroyed. Declared last so it
    /// outlives every object derived from it.
    env: EnvRegions,
}

/// A goal as seen by Python: hypotheses `(name, type)` plus the goal type.
#[pyclass]
pub struct Goal {
    #[pyo3(get)]
    pub hyps: Vec<(String, String)>,
    #[pyo3(get)]
    pub ty: String,
    #[pyo3(get)]
    pub mvar: String,
}

impl Repl {
    fn rebind<'l>(&self, lean: Lean<'l>) -> LeanResult<MetaMContext<'l>> {
        unsafe {
            Ok(MetaMContext::from_parts(
                lean,
                self.env.bind(lean),
                self.core_ctx.bind(lean),
                self.core_state.bind(lean),
                self.meta_ctx.bind(lean),
                self.meta_state.bind(lean),
            ))
        }
    }

    fn save(&mut self, metam: MetaMContext<'_>) {
        let (env, core_ctx, core_state, meta_ctx, meta_state) = metam.into_parts();
        // Swap the environment in place WITHOUT free_regions on the old env:
        // the replacement shares the old env's region buffers (environments
        // grow in place), so freeing them here would corrupt the live
        // session. Release the old env with a plain `lean_dec`; its regions
        // are freed only when the final env is dropped.
        let old_env = self.env.swap_inner(env.unbind_mt());
        drop(old_env);
        self.core_ctx = core_ctx.unbind_mt();
        self.core_state = core_state.unbind_mt();
        self.meta_ctx = meta_ctx.unbind_mt();
        self.meta_state = meta_state.unbind_mt();
    }

    /// Apply `tactic` to the `goal_idx`-th goal of `state`, appending the
    /// new replay state on success and returning its id. Shared by
    /// [`Self::run_tac`] and [`Self::try_run_tac`].
    ///
    /// On any failure (unknown state, out-of-range goal, or tactic
    /// parse/elaboration/run error) no state is appended and the session is
    /// left intact; the `LeanError` is returned for the caller to decide how
    /// to surface it.
    fn apply_tac(
        &mut self,
        lean: Lean<'_>,
        state: u64,
        tactic: &str,
        goal_idx: Option<usize>,
    ) -> LeanResult<u64> {
        let mut metam = self.rebind(lean)?;
        let st = self
            .states
            .get(state as usize)
            .ok_or_else(|| LeanError::other(&unknown_state_msg(state, self.states.len())))?;
        let idx = goal_idx.unwrap_or(0);
        let goal = st.goals.get(idx).ok_or_else(|| {
            LeanError::other(&format!(
                "no goal at index {idx} in state {state} (state has {} goals)",
                st.goals.len()
            ))
        })?;
        let goal = goal.bind(lean);
        let stx = leo3::meta::repl::parse_tactic(lean, metam.env(), tactic)?;
        // Branch from the target state's Meta.State snapshot (None →
        // run_tactic wraps metam.meta_state() in a fresh ref).
        metam.replace_meta_state(st.meta_state.bind(lean).cast());
        let outcome = run_tactic(&mut metam, &goal, &stx, None)?;
        // `Elab.runTactic` returns only the goals produced by the tactic
        // run itself; the source state's OTHER goals (multi-goal states
        // from induction/split/cases, or goals the tactic solved
        // implicitly) stay in the meta state but are not in that list.
        // Preserve them so a proof can advance goal by goal.
        let mut goals = st
            .goals
            .iter()
            .enumerate()
            .filter(|(j, _)| *j != idx)
            .map(|(_, g)| g.clone())
            .collect::<Vec<_>>();
        goals.extend(outcome.goals.into_iter().map(|g| g.unbind_mt()));
        let meta_state = metam.meta_state_snapshot();
        self.save(metam);
        self.states.push(ReplState { goals, meta_state });
        Ok((self.states.len() - 1) as u64)
    }
}

#[pymethods]
impl Repl {
    /// Create a replay session, importing the given module (default "Lean")
    /// or loading a `.lean` source file (whose top-level commands are
    /// elaborated in order; `import` lines are skipped — the Lean prelude
    /// is always imported).
    #[new]
    #[pyo3(signature = (module=None))]
    fn new(module: Option<String>) -> PyResult<Self> {
        // Serialize this import (remap cross-set bases → import → snapshots)
        // against the environment free/record sequences: their
        // `/proc/self/maps` snapshots and record steps run on caller threads
        // and would otherwise interleave with this import's remap and corrupt
        // the freed-set record. Linux-only (the stopgap is compiled out
        // elsewhere); the guard lives until the end of `new`, spanning the
        // `with_lean` import.
        #[cfg(target_os = "linux")]
        let _lifecycle = leo3::meta::lifecycle_lock();
        leo3::with_lean(|lean| -> LeanResult<Self> {
            let (metam, modules, file_vmas_added, imported_vmras, trackable) = match &module {
                Some(m) if m.ends_with(".lean") => {
                    let src = std::fs::read_to_string(m)
                        .map_err(|e| LeanError::other(&format!("cannot read {m}: {e}")))?;
                    // W-417 stopgap: re-map freed cross-set lean regions before
                    // the import's symbol lookups dereference dangling cache
                    // keys; block the import if that cannot be done safely.
                    block_on_remap(&["Lean"])?;
                    // W-417 stopgap: bracket the import with a
                    // `/proc/self/maps` snapshot to determine whether the
                    // environment is file-backed (re-mappable) or heap-backed.
                    #[cfg(target_os = "linux")]
                    let import_before = leo3::meta::snapshot_lean_vmras();
                    let env = import_modules_with_exts(lean, &["Lean"], 0, true)?;
                    let mut metam = MetaMContext::new(lean, env)?;
                    let cmds = leo3::meta::repl::parse_file_commands(lean, metam.env(), &src, m)?;
                    for stx in &cmds {
                        let env2 = leo3::meta::repl::run_command(lean, &metam, stx)?;
                        metam.replace_env(env2);
                    }
                    #[cfg(target_os = "linux")]
                    let import_after = leo3::meta::snapshot_lean_vmras();
                    let (file_vmas_added, imported_vmras, trackable) = {
                        #[cfg(target_os = "linux")]
                        {
                            // Range-based "added" (robust to metadata churn of
                            // pre-existing mappings) plus an explicit churn flag:
                            // if the import window saw a pre-existing mapping's
                            // identity change, `file_vmas_added` is unreliable and
                            // the env is marked untrackable (leaked on drop).
                            // Either snapshot unavailable -> 0/empty/untrackable
                            // so the drop gate fails closed.
                            match (&import_before, &import_after) {
                                (Ok(b), Ok(a)) => {
                                    let added = leo3::meta::diff_added_vmras(b, a);
                                    let trackable =
                                        !leo3::meta::import_window_has_identity_churn(b, a);
                                    (added.len() as u64, added, trackable)
                                }
                                _ => (0u64, Vec::new(), false),
                            }
                        }
                        #[cfg(not(target_os = "linux"))]
                        {
                            (0u64, Vec::new(), false)
                        }
                    };
                    (
                        metam,
                        vec!["Lean".to_string()],
                        file_vmas_added,
                        imported_vmras,
                        trackable,
                    )
                }
                _ => {
                    let name = module.as_deref().unwrap_or("Lean");
                    let names: &[&str] = &[name];
                    // W-417 stopgap: re-map freed cross-set lean regions before
                    // the import's symbol lookups dereference dangling cache
                    // keys; block the import if that cannot be done safely.
                    block_on_remap(names)?;
                    // W-417 stopgap: bracket the import with a
                    // `/proc/self/maps` snapshot to determine whether the
                    // environment is file-backed (re-mappable) or heap-backed.
                    #[cfg(target_os = "linux")]
                    let import_before = leo3::meta::snapshot_lean_vmras();
                    let env = import_modules_with_exts(lean, names, 0, true)?;
                    #[cfg(target_os = "linux")]
                    let import_after = leo3::meta::snapshot_lean_vmras();
                    let (file_vmas_added, imported_vmras, trackable) = {
                        #[cfg(target_os = "linux")]
                        {
                            // Range-based "added" (robust to metadata churn of
                            // pre-existing mappings) plus an explicit churn flag
                            // (see the `.lean` branch above).
                            match (&import_before, &import_after) {
                                (Ok(b), Ok(a)) => {
                                    let added = leo3::meta::diff_added_vmras(b, a);
                                    let trackable =
                                        !leo3::meta::import_window_has_identity_churn(b, a);
                                    (added.len() as u64, added, trackable)
                                }
                                _ => (0u64, Vec::new(), false),
                            }
                        }
                        #[cfg(not(target_os = "linux"))]
                        {
                            (0u64, Vec::new(), false)
                        }
                    };
                    (
                        MetaMContext::new(lean, env)?,
                        vec![name.to_string()],
                        file_vmas_added,
                        imported_vmras,
                        trackable,
                    )
                }
            };
            let (env, core_ctx, core_state, meta_ctx, meta_state) = metam.into_parts();
            Ok(Repl {
                env: EnvRegions::new(
                    env.unbind_mt(),
                    modules,
                    file_vmas_added,
                    imported_vmras,
                    trackable,
                ),
                core_ctx: core_ctx.unbind_mt(),
                core_state: core_state.unbind_mt(),
                check_counter: 0,
                meta_ctx: meta_ctx.unbind_mt(),
                meta_state: meta_state.unbind_mt(),
                states: Vec::new(),
            })
        })
        .map_err(to_py_err)
    }

    /// Create a new root goal state from a term string. The type is
    /// elaborated by Lean's real elaborator through the `suffices` tactic:
    /// create a `True` goal and replace it with `type_str` (`suffices h : t
    /// from True.intro` — the `from` proof is `True.intro`, the target type
    /// is the new goal). Existing states are unaffected; returns the new
    /// state's id (0 for the first call in a fresh session).
    fn set_goal(&mut self, type_str: &str) -> PyResult<u64> {
        leo3::with_lean(|lean| -> LeanResult<u64> {
            let mut metam = self.rebind(lean)?;
            let true_const = LeanExpr::const_(
                lean,
                LeanName::from_str(lean, "True")?,
                LeanList::nil(lean)?,
            )?;
            let goal = metam.mk_goal(&true_const)?;
            let mvar = LeanExpr::mvar_id(&goal)?;
            let tac = format!("suffices h : {type_str} from True.intro");
            let stx = leo3::meta::repl::parse_tactic(lean, metam.env(), &tac)?;
            let outcome = run_tactic(&mut metam, &mvar, &stx, None)?;
            let goals = outcome
                .goals
                .into_iter()
                .map(|g| g.unbind_mt())
                .collect::<Vec<_>>();
            let meta_state = metam.meta_state_snapshot();
            self.save(metam);
            self.states.push(ReplState { goals, meta_state });
            Ok((self.states.len() - 1) as u64)
        })
        .map_err(to_py_err)
    }

    /// Apply a tactic to the `goal_idx`-th goal of `state` (default 0);
    /// returns the new state id. Multi-goal states (induction/split/cases)
    /// can be advanced goal by goal in any order.
    #[pyo3(signature = (state, tactic, goal_idx=None))]
    fn run_tac(&mut self, state: u64, tactic: &str, goal_idx: Option<usize>) -> PyResult<u64> {
        leo3::with_lean(|lean| self.apply_tac(lean, state, tactic, goal_idx)).map_err(to_py_err)
    }

    /// Non-raising variant of [`Self::run_tac`]: returns
    /// `(state_id, success)` instead of raising `RuntimeError`.
    ///
    /// On success the new replay state id is returned with `true`. On
    /// failure (unknown state, out-of-range goal, or tactic
    /// parse/elaboration/run error) the source `state` id is returned with
    /// `false` and no new state is appended — the session and the replay
    /// state stay usable. This is the core idiom for proof-search / RL
    /// loops ("try a tactic, learn whether it succeeded"):
    ///
    /// ```python
    /// s2, ok = repl.try_run_tac(s1, "simp")
    /// ```
    #[pyo3(signature = (state, tactic, goal_idx=None))]
    fn try_run_tac(&mut self, state: u64, tactic: &str, goal_idx: Option<usize>) -> (u64, bool) {
        match leo3::with_lean(|lean| self.apply_tac(lean, state, tactic, goal_idx)) {
            Ok(new_state) => (new_state, true),
            Err(_) => (state, false),
        }
    }

    /// Number of remaining goals in `state`.
    fn get_num_goals(&self, state: u64) -> PyResult<usize> {
        let st = self
            .states
            .get(state as usize)
            .ok_or_else(|| PyRuntimeError::new_err(unknown_state_msg(state, self.states.len())))?;
        Ok(st.goals.len())
    }

    /// The remaining goals of `state` as a list of `Goal` objects.
    fn get_goals(&self, state: u64) -> PyResult<Vec<Goal>> {
        let st = self
            .states
            .get(state as usize)
            .ok_or_else(|| PyRuntimeError::new_err(unknown_state_msg(state, self.states.len())))?;
        leo3::with_lean(|lean| -> LeanResult<Vec<Goal>> {
            let mut metam = self.rebind(lean)?;
            let mut out = Vec::new();
            for g in &st.goals {
                let gb = g.bind(lean);
                // Hypothesis types and the goal type are pretty-printed with
                // Lean's real pretty printer (user-facing names, notations).
                let (hyps, ty_pp) = metam.goal_hyps_and_type_pp(&gb)?;
                let mvar_str = leo3_name_to_string(lean, &gb)?;
                out.push(Goal {
                    hyps,
                    ty: ty_pp,
                    mvar: mvar_str,
                });
            }
            Ok(out)
        })
        .map_err(to_py_err)
    }

    /// Pretty-print a goal with Lean's real pretty printer (delaborator +
    /// pretty printer): hypotheses followed by the goal type, using the
    /// user-facing variable names and the usual notations.
    #[pyo3(signature = (state, goal_idx=None))]
    fn get_goal_pp(&self, state: u64, goal_idx: Option<usize>) -> PyResult<String> {
        let idx = goal_idx.unwrap_or(0);
        let st = self
            .states
            .get(state as usize)
            .ok_or_else(|| PyRuntimeError::new_err(unknown_state_msg(state, self.states.len())))?;
        let g = st.goals.get(idx).ok_or_else(|| {
            PyRuntimeError::new_err(format!(
                "no goal at index {idx} in state {state} (state has {} goals)",
                st.goals.len()
            ))
        })?;
        leo3::with_lean(|lean| -> LeanResult<String> {
            let mut metam = self.rebind(lean)?;
            let gb = g.bind(lean);
            leo3::meta::repl::pp_goal(&mut metam, &gb)
        })
        .map_err(to_py_err)
    }

    /// Check whether the environment has a constant.
    fn env_has_const(&self, name: &str) -> PyResult<bool> {
        leo3::with_lean(|lean| -> LeanResult<bool> {
            let env = self.env.bind(lean);
            let n = LeanName::from_components(lean, name)?;
            Ok(LeanEnvironment::find(&env, &n)?.is_some())
        })
        .map_err(to_py_err)
    }

    /// Execute a Lean command (e.g. `def`, `theorem`, `axiom`, `open`) in
    /// the current environment, updating it. Returns nothing: commands do
    /// not create replay states — use the state ids returned by
    /// `set_goal`/`run_tac` (see `num_states`).
    ///
    /// The command is parsed with Lean's real parser and elaborated by the
    /// embedded `Lean.Elab.Command.elabCommandTopLevel` frontend; the
    /// resulting environment is installed for subsequent calls. Commands
    /// that fail elaboration raise `RuntimeError` (the replay session stays
    /// intact). Note: command output (`#print`, `#check`, `#eval`, ...) is
    /// not captured — use `inspect` / `check` for declaration and term
    /// queries, and only run environment-mutating commands here.
    fn run_cmd(&mut self, cmd: &str) -> PyResult<()> {
        leo3::with_lean(|lean| -> LeanResult<()> {
            let mut metam = self.rebind(lean)?;
            let stx = leo3::meta::repl::parse_command(lean, metam.env(), cmd)?;
            let env2 = leo3::meta::repl::run_command(lean, &metam, &stx)?;
            metam.replace_env(env2);
            self.save(metam);
            Ok(())
        })
        .map_err(to_py_err)
    }

    /// Number of replay states created so far (`0` before the first
    /// `set_goal`). Valid state ids are `0..num_states()` (half-open — the
    /// highest valid id is `num_states() - 1`).
    fn num_states(&self) -> usize {
        self.states.len()
    }

    /// `#check`-style query: return the type of `term` in the requested
    /// context, rendered as `"{term} : {type}"` by Lean's real pretty
    /// printer.
    ///
    /// - `state=None`: the root context — `state 0`'s context after
    ///   `set_goal`, or the imported modules only before it.
    /// - `state=N, goal_idx=K`: the local context of that goal
    ///   (hypotheses introduced so far are in scope).
    ///
    /// A bare constant (e.g. `List.map`) behaves like the real `#check`:
    /// it is elaborated with no expected type, so its universe and
    /// implicit arguments remain binders — the printed type is the
    /// declaration's declared type. Any other term is elaborated in the
    /// goal's local context.
    ///
    /// Name resolution follows Lean: a local hypothesis that shadows the
    /// name — including a prefix shadow of a qualified name (a local
    /// `List` also shadows `List.map`) — resolves to the local
    /// declaration, not the global constant.
    ///
    /// Names are resolved at the meta level, so fully qualified names are
    /// required (command-level scopes such as `open` do not apply).
    /// Elaboration failures (unknown identifiers, type errors) raise
    /// `RuntimeError` with Lean's error message; the replay session is not
    /// modified.
    #[pyo3(signature = (term, state=None, goal_idx=None))]
    fn check(
        &mut self,
        term: &str,
        state: Option<u64>,
        goal_idx: Option<usize>,
    ) -> PyResult<String> {
        leo3::with_lean(|lean| -> LeanResult<String> {
            let mut metam = self.rebind(lean)?;
            // Resolve (and validate) the requested goal context. The goal
            // is only needed to elaborate non-constant terms; a bare
            // constant's type is environment-fixed.
            let goal: Option<LeanBound<'_, LeanName>> = match state {
                Some(state) => {
                    let st = self.states.get(state as usize).ok_or_else(|| {
                        LeanError::other(&unknown_state_msg(state, self.states.len()))
                    })?;
                    let idx = goal_idx.unwrap_or(0);
                    let g = st.goals.get(idx).ok_or_else(|| {
                        LeanError::other(&format!(
                            "no goal at index {idx} in state {state} (state has {} goals)",
                            st.goals.len()
                        ))
                    })?;
                    metam.replace_meta_state(st.meta_state.bind(lean).cast());
                    Some(g.bind(lean))
                }
                None => {
                    if let Some(st0) = self.states.first() {
                        metam.replace_meta_state(st0.meta_state.bind(lean).cast());
                    }
                    None
                }
            };
            // Name resolution: if a local hypothesis of the target goal
            // shadows the term's name (or a prefix of it — a local
            // `List` also shadows `List.map`), the name resolves to the
            // local declaration, and the constant fast path below would
            // wrongly return the global declaration's type. Skip it in
            // that case; the `have`-based elaboration resolves names the
            // way Lean does (locals first).
            let shadowed = match &goal {
                Some(g) => {
                    let (hyps, _ty) = metam.goal_hyps_and_type_pp(g)?;
                    let mut prefix = String::new();
                    let mut shadowed = false;
                    for part in term.split('.') {
                        if !prefix.is_empty() {
                            prefix.push('.');
                        }
                        prefix.push_str(part);
                        if hyps.iter().any(|(name, _)| name == &prefix) {
                            shadowed = true;
                            break;
                        }
                    }
                    shadowed
                }
                None => false,
            };
            // `#check` semantics for a bare constant: the real `#check`
            // elaborates it with no expected type, leaving its universe
            // and implicit arguments as binders, so the printed type is
            // the declaration's declared type. Elaborating via `have`
            // instead would require synthesizing every implicit argument
            // and reject such constants (e.g. `List.map`), so resolve
            // them from the environment directly.
            let env = self.env.bind(lean);
            if !shadowed {
                if let Ok(nm) = LeanName::from_components(lean, term) {
                    if let Some(cinfo) = LeanEnvironment::find(&env, &nm)? {
                        let ty = LeanConstantInfo::type_(&cinfo)?;
                        let rendered =
                            pp_exprs(&metam, &empty_lctx(lean), &empty_insts(lean), &[ty])?;
                        return Ok(format!("{term} : {}", rendered[0]));
                    }
                }
            }
            // Otherwise elaborate the term as a local declaration in the
            // goal's local context; its type (the last hypothesis of the
            // tactic's resulting goal) is the term's type. `runTactic`
            // yields a FRESH goal mvar carrying the updated local context
            // — the source mvar is left untouched — so the hypothesis
            // must be read from the tactic's outcome, not from the
            // original goal.
            let goal = match goal {
                Some(g) => g,
                None => {
                    let true_const = LeanExpr::const_(
                        lean,
                        LeanName::from_str(lean, "True")?,
                        LeanList::nil(lean)?,
                    )?;
                    let g = metam.mk_goal(&true_const)?;
                    LeanExpr::mvar_id(&g)?
                }
            };
            self.check_counter += 1;
            let decl_name = format!("h_leotower_check_{}", self.check_counter);
            let tac = format!("have {decl_name} := {term}");
            let stx = leo3::meta::repl::parse_tactic(lean, metam.env(), &tac)?;
            let outcome = run_tactic(&mut metam, &goal, &stx, None)?;
            let goal_after =
                outcome.goals.first().cloned().ok_or_else(|| {
                    LeanError::other("internal error: check have produced no goals")
                })?;
            let (hyps, _ty) = metam.goal_hyps_and_type_pp(&goal_after)?;
            let (_, pp_type) = hyps.last().ok_or_else(|| {
                LeanError::other("internal error: check declaration not found in goal context")
            })?;
            Ok(format!("{term} : {pp_type}"))
        })
        .map_err(to_py_err)
    }

    /// `#print`-style query: show a declaration's kind, type, and (for
    /// definitions/theorems/opaque constants) its value, all rendered by
    /// Lean's real pretty printer. Unknown declarations raise
    /// `RuntimeError`.
    fn inspect(&self, name: &str) -> PyResult<String> {
        leo3::with_lean(|lean| -> LeanResult<String> {
            let metam = self.rebind(lean)?;
            let env = self.env.bind(lean);
            let nm = LeanName::from_components(lean, name)?;
            let cinfo = LeanEnvironment::find(&env, &nm)?
                .ok_or_else(|| LeanError::other(&format!("unknown constant: {name}")))?;
            let kind = LeanConstantInfo::kind(&cinfo);
            let ty = LeanConstantInfo::type_(&cinfo)?;
            let value = LeanConstantInfo::value(&cinfo)?;
            // Top-level declarations are closed: pretty-print with an
            // empty local context / local instances.
            let mut exprs = vec![ty];
            if let Some(v) = value {
                exprs.push(v);
            }
            let rendered = pp_exprs(&metam, &empty_lctx(lean), &empty_insts(lean), &exprs)?;
            let label = match kind {
                ConstantKind::Inductive => "inductive",
                ConstantKind::Axiom => "axiom",
                ConstantKind::Opaque => "opaque",
                ConstantKind::Theorem => "theorem",
                ConstantKind::Definition => "def",
                ConstantKind::Constructor => "def",
                ConstantKind::Recursor => "def",
                ConstantKind::Quot => "def",
            };
            let mut out = format!("{label} {name} : {}", rendered[0]);
            if rendered.len() > 1 {
                out.push_str(&format!(" :=\n{}", rendered[1]));
            }
            Ok(out)
        })
        .map_err(to_py_err)
    }
}

/// `Lean.Name.toString : Name → String` (curried arity-1 pure function).
fn leo3_name_to_string<'l>(lean: Lean<'l>, name: &LeanBound<'l, LeanName>) -> LeanResult<String> {
    unsafe {
        extern "C" {
            #[link_name = "l_Lean_Name_toString"]
            fn name_to_string(
                env: *mut *mut ffi::lean_object,
                arg: *mut ffi::lean_object,
            ) -> *mut ffi::lean_object;
        }
        ffi::lean_inc(name.as_ptr());
        let closure =
            ffi::inline::lean_alloc_closure(name_to_string as *mut std::ffi::c_void, 1u32, 0);
        let s = ffi::closure::lean_apply_1(closure, name.as_ptr());
        let s = LeanBound::<LeanString>::from_owned_ptr(lean, s);
        Ok(LeanString::cstr(&s)?.to_string())
    }
}

/// Empty local context for pretty-printing closed (top-level) expressions.
fn empty_lctx<'l>(lean: Lean<'l>) -> LeanBound<'l, LeanAny> {
    unsafe { LeanBound::from_owned_ptr(lean, ffi::meta::lean_mk_empty_local_ctx(ffi::lean_box(0))) }
}

/// Empty local-instance context for pretty-printing closed expressions.
fn empty_insts<'l>(lean: Lean<'l>) -> LeanBound<'l, LeanAny> {
    unsafe { LeanBound::from_owned_ptr(lean, ffi::array::lean_mk_empty_array()) }
}

/// `leotower._leotower` — the native extension module.
#[pymodule]
fn _leotower(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(prepare_freethreaded_lean, m)?)?;
    m.add_class::<LeanSession>()?;
    m.add_class::<Repl>()?;
    m.add_class::<Goal>()?;
    Ok(())
}

#[cfg(all(test, target_os = "linux"))]
mod quarantine_test {
    use super::*;

    /// Count the `/proc/self/maps` lines backed by a lean import-region file.
    fn lean_file_vma_count() -> u64 {
        std::fs::read_to_string("/proc/self/maps")
            .map(|maps| {
                maps.lines()
                    .filter(|l| {
                        let path = l.split_whitespace().nth(5).unwrap_or("");
                        path.ends_with(".olean")
                            || path.ends_with(".ir")
                            || path.ends_with(".server")
                            || path.ends_with(".private")
                    })
                    .count() as u64
            })
            .unwrap_or(0)
    }

    #[test]
    fn drop_leaks_when_quarantined() {
        // Once the keepalive is quarantined (a prior destructive `free_regions`
        // failed in a way that could not be proven fully recovered), a
        // file-backed env must LEAK on drop — no `free_regions` — because
        // freeing could create more dangling keys that no re-map would revive.
        // This exercises the *real* destructor path. It poisons the
        // process-wide one-way latch, so it must be the last test to run in
        // this binary (leotower currently has no other Rust tests).
        let (env, file_vmas, imported) = leo3::test_with_lean(|lean| {
            let before = leo3::meta::snapshot_lean_vmras().expect("maps readable");
            let env = import_modules_with_exts(lean, &["Lean"], 0, true)
                .expect("import Lean")
                .unbind_mt();
            let after = leo3::meta::snapshot_lean_vmras().expect("maps readable");
            let added = leo3::meta::diff_added_vmras(&before, &after);
            (env, added.len() as u64, added)
        });
        let before = lean_file_vma_count();
        let regions = EnvRegions::new(env, vec!["Lean".to_string()], file_vmas, imported, true);
        leo3::meta::poison_keepalive();
        assert!(leo3::meta::keepalive_poisoned());
        std::mem::drop(regions); // poisoned -> leak, no free_regions
        assert_eq!(
            lean_file_vma_count(),
            before,
            "a quarantined drop must leak the env (no free_regions); the file VMAs stay mapped"
        );
        // Import boundary (item 1): a subsequent import must be REFUSED while
        // the keepalive is quarantined — it would walk the symbol cache and
        // dereference dangling keys. The refusal happens at
        // `import_modules_with_exts` itself, not just in leotower's pre-import
        // re-map hook.
        let import = leo3::test_with_lean(|lean| {
            leo3::meta::repl::import_modules_with_exts(lean, &["Lean"], 0, true)
                .map(|b| b.unbind_mt())
        });
        assert!(
            import.is_err(),
            "a quarantined import must be refused at the leo3 import boundary"
        );
    }
}
