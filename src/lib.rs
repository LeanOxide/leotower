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

use leo3::meta::context::{CoreContext, CoreState, MetaContext, MetaState};
use leo3::meta::environment::LeanEnvironment;
use leo3::meta::expr::LeanExpr;
use leo3::meta::metam::MetaMContext;
use leo3::meta::name::LeanName;
use leo3::meta::repl::{import_modules_with_exts, run_tactic};
use leo3::instance::LeanAny;
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
            let mut metam = match &module {
                Some(m) if m.ends_with(".lean") => {
                    let src = std::fs::read_to_string(m).map_err(|e| {
                        LeanError::other(&format!("cannot read {m}: {e}"))
                    })?;
                    let env = import_modules_with_exts(lean, &["Lean"], 0, true)?;
                    let mut metam = MetaMContext::new(lean, env)?;
                    let cmds = leo3::meta::repl::parse_file_commands(
                        lean, metam.env(), &src, m,
                    )?;
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
                meta_ctx: meta_ctx.unbind_mt(),
                meta_state: meta_state.unbind_mt(),
                states: Vec::new(),
            })
        })
        .map_err(to_py_err)
    }

    /// Set the root goal from a term string. The type is elaborated by
    /// Lean's real elaborator through the `suffices` tactic: create a `True`
    /// goal and replace it with `type_str` (`suffices h : t from True.intro`
    /// — the `from` proof is `True.intro`, the target type is the new goal).
    /// Returns state 0.
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
            self.states.push(ReplState {
                goals,
                meta_state,
            });
            Ok((self.states.len() - 1) as u64)
        })
        .map_err(to_py_err)
    }

    /// Apply a tactic to the first goal of `state`; returns the new state id.
    fn run_tac(&mut self, state: u64, tactic: &str) -> PyResult<u64> {
        leo3::with_lean(|lean| -> LeanResult<u64> {
            let mut metam = self.rebind(lean)?;
            let st = self
                .states
                .get(state as usize)
                .ok_or_else(|| LeanError::other("unknown state"))?;
            let goal = st
                .goals
                .first()
                .ok_or_else(|| LeanError::other("no goals left in this state"))?;
            let goal = goal.bind(lean);
            let stx = leo3::meta::repl::parse_tactic(lean, metam.env(), tactic)?;
            // Branch from the target state's Meta.State snapshot (None →
            // run_tactic wraps metam.meta_state() in a fresh ref).
            metam.replace_meta_state(unsafe { st.meta_state.bind(lean).cast() });
            let outcome = run_tactic(&mut metam, &goal, &stx, None)?;
            let goals = outcome
                .goals
                .into_iter()
                .map(|g| g.unbind_mt())
                .collect::<Vec<_>>();
            let meta_state = metam.meta_state_snapshot();
            self.save(metam);
            self.states.push(ReplState {
                goals,
                meta_state,
            });
            Ok((self.states.len() - 1) as u64)
        })
        .map_err(to_py_err)
    }

    /// Number of remaining goals in `state`.
    fn get_num_goals(&self, state: u64) -> PyResult<usize> {
        let st = self
            .states
            .get(state as usize)
            .ok_or_else(|| PyRuntimeError::new_err("unknown state"))?;
        Ok(st.goals.len())
    }

    /// The remaining goals of `state` as a list of `Goal` objects.
    fn get_goals(&self, state: u64) -> PyResult<Vec<Goal>> {
        let st = self
            .states
            .get(state as usize)
            .ok_or_else(|| PyRuntimeError::new_err("unknown state"))?;
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
            .ok_or_else(|| PyRuntimeError::new_err("unknown state"))?;
        let g = st
            .goals
            .get(idx)
            .ok_or_else(|| PyRuntimeError::new_err("no such goal"))?;
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

    /// Execute a Lean command (e.g. `example`, `theorem`, `def`, `open`) in
    /// the current environment, updating it. Returns a new state id (the
    /// tactic-goal state is unchanged).
    ///
    /// The command is parsed with Lean's real parser and elaborated by the
    /// embedded `Lean.Elab.Command.elabCommandTopLevel` frontend; the
    /// resulting environment is installed for subsequent calls. Commands
    /// that fail elaboration raise `RuntimeError` (the replay session stays
    /// intact).
    fn run_cmd(&mut self, cmd: &str) -> PyResult<u64> {
        leo3::with_lean(|lean| -> LeanResult<u64> {
            let mut metam = self.rebind(lean)?;
            let stx = leo3::meta::repl::parse_command(lean, metam.env(), cmd)?;
            let env2 = leo3::meta::repl::run_command(lean, &metam, &stx)?;
            metam.replace_env(env2);
            self.save(metam);
            // Tactic-goal states are untouched by command execution.
            Ok(self.states.len().saturating_sub(1) as u64)
        })
        .map_err(to_py_err)
    }
}

/// `Lean.Name.toString : Name → String` (curried arity-1 pure function).
fn leo3_name_to_string<'l>(
    lean: Lean<'l>,
    name: &LeanBound<'l, LeanName>,
) -> LeanResult<String> {
    unsafe {
        extern "C" {
            #[link_name = "l_Lean_Name_toString"]
            fn name_to_string(
                env: *mut *mut ffi::lean_object,
                arg: *mut ffi::lean_object,
            ) -> *mut ffi::lean_object;
        }
        ffi::lean_inc(name.as_ptr());
        let closure = ffi::inline::lean_alloc_closure(
            name_to_string as *mut std::ffi::c_void,
            1u32,
            0,
        );
        let s = ffi::closure::lean_apply_1(closure, name.as_ptr());
        let s = LeanBound::<LeanString>::from_owned_ptr(lean, s);
        Ok(LeanString::cstr(&s)?.to_string())
    }
}

/// Parse a command string in the `command` parser category.
fn parse_command<'l>(
    lean: Lean<'l>,
    env: &LeanBound<'l, LeanEnvironment>,
    input: &str,
) -> LeanResult<LeanBound<'l, LeanExpr>> {
    unsafe {
        let cat = LeanName::from_str(lean, "command")?;
        let input_obj = LeanString::mk(lean, input)?;
        let file = LeanString::mk(lean, "<stdin>")?;

        let result = leo3_apply_curried(
            leo3::ffi::meta::repl::lean_parser_run_parser_category as *mut std::ffi::c_void,
            4,
            &[
                {
                    ffi::lean_inc(env.as_ptr());
                    env.as_ptr()
                },
                cat.into_ptr(),
                input_obj.into_ptr(),
                file.into_ptr(),
            ],
        );
        if ffi::lean_obj_tag(result) == 1 {
            let syntax = ffi::lean_ctor_get(result, 0) as *mut ffi::lean_object;
            ffi::lean_inc(syntax);
            ffi::lean_dec(result);
            Ok(LeanBound::from_owned_ptr(lean, syntax))
        } else {
            let err = ffi::lean_ctor_get(result, 0) as *mut ffi::lean_object;
            let c_str = ffi::inline::lean_string_cstr(err);
            let message = if c_str.is_null() {
                "<unprintable>".to_string()
            } else {
                std::ffi::CStr::from_ptr(c_str).to_string_lossy().into_owned()
            };
            ffi::lean_dec(result);
            Err(LeanError::other(format!("command parse error: {message}").as_str()))
        }
    }
}

/// Apply a curried Lean function object/code entry with `arity` arguments
/// (mirrors leo3's internal helper; `l_` symbols are code entries or closure
/// objects, detected by tag).
unsafe fn leo3_apply_curried(
    fn_ptr: *mut std::ffi::c_void,
    arity: usize,
    args: &[*mut ffi::lean_object],
) -> *mut ffi::lean_object {
    debug_assert_eq!(args.len(), arity);
    let fn_obj = fn_ptr as *mut ffi::lean_object;
    if ffi::inline::lean_is_closure(fn_obj) {
        match arity {
            1 => ffi::closure::lean_apply_1(fn_obj, args[0]),
            2 => ffi::closure::lean_apply_2(fn_obj, args[0], args[1]),
            3 => ffi::closure::lean_apply_3(fn_obj, args[0], args[1], args[2]),
            4 => ffi::closure::lean_apply_4(fn_obj, args[0], args[1], args[2], args[3]),
            _ => unreachable!(),
        }
    } else {
        let closure = ffi::inline::lean_alloc_closure(fn_ptr, arity as u32, 0);
        match arity {
            1 => ffi::closure::lean_apply_1(closure, args[0]),
            2 => ffi::closure::lean_apply_2(closure, args[0], args[1]),
            3 => ffi::closure::lean_apply_3(closure, args[0], args[1], args[2]),
            4 => ffi::closure::lean_apply_4(closure, args[0], args[1], args[2], args[3]),
            _ => unreachable!(),
        }
    }
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
