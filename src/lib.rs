//! Python bindings for Leo3 — safe, ergonomic Rust bindings for the Lean4
//! theorem prover.
//!
//! This is the native extension module `leotower._leotower`.  The ergonomic
//! Python-facing surface lives in `python/leotower/__init__.py`.

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

/// `leotower._leotower` — the native extension module.
#[pymodule]
fn _leotower(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(prepare_freethreaded_lean, m)?)?;
    m.add_class::<LeanSession>()?;
    Ok(())
}
