"""leotower: Python bindings for Leo3 — safe, ergonomic Rust bindings for the Lean4 theorem prover.

Usage:

    import leotower

    with leotower.with_lean() as lean:
        assert lean.nat_add(20, 22) == 42
        assert lean.pow_str(2, 100) == "1267650600228229401496703205376"

All operations run inside Lean's real runtime.  Session methods are safe to
call from any Python thread while it holds the GIL: each OS thread attaches
to the shared Lean runtime on first use.
"""

from contextlib import contextmanager

from leotower._leotower import LeanSession, prepare_freethreaded_lean

__all__ = ["with_lean", "LeanSession", "prepare_freethreaded_lean"]


@contextmanager
def with_lean():
    """Enter the shared Lean runtime and yield a :class:`LeanSession`.

    Ensures the one-time runtime bootstrap (worker thread) has run, then
    attaches the calling thread.  Lean objects created through the session
    live in Lean's runtime and are reclaimed by Lean's own GC.
    """
    prepare_freethreaded_lean()
    yield LeanSession()
