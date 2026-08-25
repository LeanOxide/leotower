//! Python bindings for Leo3 — safe, ergonomic Rust bindings for the Lean4
//! theorem prover.
//!
//! This is the native extension module `leotower._leotower`.  The ergonomic
//! Python-facing surface lives in `python/leotower/__init__.py`.

use leo3::ffi;
use leo3::prelude::*;
use pyo3::exceptions::PyRuntimeError;
use pyo3::prelude::*;

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

/// A LeanDojo-style replay session over the embedded Lean runtime.
///
/// State 0 is the root: after `set_goal` it holds the initial goal. Each
/// `run_tac` appends a new state; `get_goals(state)` / `get_num_goals(state)`
/// / `get_goal_pp(state)` inspect it. Invalid tactics raise `RuntimeError`
/// instead of crashing the interpreter.
#[pyclass]
pub struct Repl {
    env: LeanUnbound<LeanEnvironment>,
    core_ctx: LeanUnbound<CoreContext>,
    core_state: LeanUnbound<CoreState>,
    /// Monotonic counter for the `have`-declaration names used by
    /// [`Self::check`] (guarantees a fresh name per call).
    check_counter: u64,
    meta_ctx: LeanUnbound<MetaContext>,
    meta_state: LeanUnbound<MetaState>,
    states: Vec<ReplState>,
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
        self.env = env.unbind_mt();
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
        leo3::with_lean(|lean| -> LeanResult<Self> {
            let metam = match &module {
                Some(m) if m.ends_with(".lean") => {
                    let src = std::fs::read_to_string(m)
                        .map_err(|e| LeanError::other(&format!("cannot read {m}: {e}")))?;
                    let env = import_modules_with_exts(lean, &["Lean"], 0, true)?;
                    let mut metam = MetaMContext::new(lean, env)?;
                    let cmds = leo3::meta::repl::parse_file_commands(lean, metam.env(), &src, m)?;
                    for stx in &cmds {
                        let env2 = leo3::meta::repl::run_command(lean, &metam, stx)?;
                        metam.replace_env(env2);
                    }
                    metam
                }
                _ => {
                    let names: &[&str] = &[module.as_deref().unwrap_or("Lean")];
                    let env = import_modules_with_exts(lean, names, 0, true)?;
                    MetaMContext::new(lean, env)?
                }
            };
            let (env, core_ctx, core_state, meta_ctx, meta_state) = metam.into_parts();
            Ok(Repl {
                env: env.unbind_mt(),
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
