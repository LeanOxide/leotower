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


# ============================================================================
# Repl — LeanDojo-compatible replay layer
# ============================================================================

from leotower._leotower import Goal as _Goal
from leotower._leotower import Repl as _Repl


class Goal:
    """A goal: hypotheses as ``(name, type)`` pairs plus the goal type."""

    __slots__ = ("hyps", "ty", "mvar")

    def __init__(self, hyps, ty, mvar):
        self.hyps = list(hyps)
        self.ty = ty
        self.mvar = mvar

    def __repr__(self):
        return f"Goal({self.hyps!r} ⊢ {self.ty})"


class Repl:
    """A LeanDojo-style replay session over the embedded Lean runtime.

    Examples:
        >>> repl = Repl()
        >>> s0 = repl.set_goal("∀ n m : Nat, n + m = m + n")
        >>> repl.get_num_goals(s0)
        1
        >>> s1 = repl.run_tac(s0, "intro n m")
        >>> repl.get_num_goals(s1)
        1
    """

    def __init__(self, module: str = "Lean"):
        self._repl = _Repl(module)

    # -- state management ---------------------------------------------------
    def set_goal(self, type_str: str) -> int:
        """Set the root goal from a term string; returns state 0."""
        return self._repl.set_goal(type_str)

    def run_tac(self, state: int, tactic: str) -> int:
        """Apply ``tactic`` to the first goal of ``state``; returns the new
        state id.  Invalid tactics raise :class:`RuntimeError` (the
        interpreter and the replay state stay intact)."""
        return self._repl.run_tac(state, tactic)

    def run_cmd(self, cmd: str) -> int:
        """Execute a Lean command in the current environment.

        Commands are parsed with Lean's real parser; full command
        elaboration is not yet available in the embedded bridge and raises
        :class:`RuntimeError`.
        """
        return self._repl.run_cmd(cmd)

    # -- goal queries -------------------------------------------------------
    def get_num_goals(self, state: int) -> int:
        return self._repl.get_num_goals(state)

    def get_goals(self, state: int):
        raw = self._repl.get_goals(state)
        return [Goal(g.hyps, g.ty, g.mvar) for g in raw]

    def get_goal_pp(self, state: int, goal_idx: int = 0) -> str:
        return self._repl.get_goal_pp(state, goal_idx)

    # -- environment queries ------------------------------------------------
    def env_has_const(self, name: str) -> bool:
        return self._repl.env_has_const(name)


__all__ += ["Repl", "Goal"]
