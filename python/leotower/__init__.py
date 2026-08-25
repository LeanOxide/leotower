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

import os
import sys

from contextlib import contextmanager


def _extend_windows_dll_search_path() -> None:
    """Add the Lean toolchain's bin dir to the DLL search path (Windows).

    The native extension links Lean's shared libraries
    (``libleanshared*.dll``, ``libInit_shared.dll``), which live in the
    Lean toolchain's ``bin`` dir.  The Windows loader does not reliably
    resolve them from ``PATH`` (verified on GitHub-hosted runners),
    whereas directories registered with :func:`os.add_dll_directory`
    always do — and the registration is what end users need too, since
    the published wheel does not bundle the Lean DLLs.

    Candidates: ``$LEAN_HOME/bin``, then every elan toolchain dir under
    ``%USERPROFILE%\\.elan\\toolchains``.  Only directories that
    actually contain ``libleanshared.dll`` are added.
    """
    if sys.platform != "win32":
        return
    candidates = []
    lean_home = os.environ.get("LEAN_HOME")
    if lean_home:
        candidates.append(os.path.join(lean_home, "bin"))
    userprofile = os.environ.get("USERPROFILE")
    if userprofile:
        toolchains = os.path.join(userprofile, ".elan", "toolchains")
        if os.path.isdir(toolchains):
            candidates.extend(
                os.path.join(toolchains, name, "bin")
                for name in sorted(os.listdir(toolchains))
            )
    for directory in candidates:
        if os.path.isfile(os.path.join(directory, "libleanshared.dll")):
            os.add_dll_directory(directory)


_extend_windows_dll_search_path()

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
        """LeanDojo-style replay session.

        ``module`` is a Lean module name (imported from the Lean search
        path, default "Lean") or the path of a ``.lean`` file whose
        top-level commands are elaborated into the session environment
        (``import`` lines are skipped).
        """
        self._repl = _Repl(module)

    # -- state management ---------------------------------------------------
    def set_goal(self, type_str: str) -> int:
        """Set the root goal from a term string; returns state 0."""
        return self._repl.set_goal(type_str)

    def run_tac(self, state: int, tactic: str, goal_idx: int = 0) -> int:
        """Apply ``tactic`` to the ``goal_idx``-th goal of ``state`` (default
        0); returns the new state id.  Multi-goal states (from ``induction``,
        ``split``, ``cases``) keep their unworked goals in the new state, so
        a proof can advance goal by goal in any order.  Invalid tactics
        raise :class:`RuntimeError` (the interpreter and the replay state
        stay intact)."""
        return self._repl.run_tac(state, tactic, goal_idx)

    def run_cmd(self, cmd: str) -> None:
        """Execute a Lean command in the current environment.

        The command is parsed with Lean's real parser and elaborated by the
        embedded frontend (``Lean.Elab.Command.elabCommandTopLevel``); the
        resulting environment is installed for subsequent calls. Commands
        that fail elaboration raise :class:`RuntimeError` (the session stays
        usable). Commands do not create replay states and return nothing —
        use :meth:`inspect` / :meth:`check` for declaration and term
        queries, and only run environment-mutating commands here.
        """
        self._repl.run_cmd(cmd)

    # -- goal queries -------------------------------------------------------
    def get_num_goals(self, state: int) -> int:
        return self._repl.get_num_goals(state)

    def get_goals(self, state: int):
        raw = self._repl.get_goals(state)
        return [Goal(g.hyps, g.ty, g.mvar) for g in raw]

    def get_goal_pp(self, state: int, goal_idx: int = 0) -> str:
        return self._repl.get_goal_pp(state, goal_idx)

    def run_tacs(self, state: int, tactics: "list[str]", goal_idx: int = 0) -> int:
        """Apply a sequence of tactics in order to the ``goal_idx``-th goal,
        starting from ``state``; returns the final state id.  This is the
        replay/RL loop idiom — apply ``[t1, t2, ...]`` without threading
        intermediate state ids by hand.  Tactics are applied left to right;
        the first one to fail raises :class:`RuntimeError` and the returned
        state is that of the last successful tactic (the session stays
        usable).  If ``tactics`` is empty, ``state`` is returned unchanged.
        """
        cur = state
        for tac in tactics:
            cur = self.run_tac(cur, tac, goal_idx)
        return cur

    # -- replay introspection -----------------------------------------------
    def num_states(self) -> int:
        """Number of replay states created so far (``0`` before the first
        :meth:`set_goal`).  Valid state ids are ``0..num_states()``."""
        return self._repl.num_states()

    # -- queries -------------------------------------------------------------
    def check(self, term: str, state: int | None = None, goal_idx: int = 0) -> str:
        """``#check``-style query: elaborate ``term`` as a term and return
        ``"{term} : {type}"`` with the type rendered by Lean's real pretty
        printer.

        With ``state=None`` the term is checked in the root context
        (``state 0``'s context after :meth:`set_goal`, or the imported
        modules only before it).  With ``state=N`` (and optional
        ``goal_idx=K``) it is checked in that goal's local context, so
        hypotheses introduced so far are in scope.

        A bare constant (e.g. ``List.map``) is elaborated the way the
        real ``#check`` does — with no expected type, so its universe
        and implicit arguments remain binders and the printed type is
        the declaration's declared type.  Any other term is elaborated
        in the goal's local context.

        Names are resolved at the meta level: use fully qualified names
        (command-level scopes such as ``open`` do not apply). Elaboration
        failures (unknown identifiers, type errors) raise
        :class:`RuntimeError` with Lean's error message; the replay session
        is not modified.

        >>> repl.check("Nat.add")
        'Nat.add : Nat → Nat → Nat'
        """
        return self._repl.check(term, state, goal_idx)

    def inspect(self, name: str) -> str:
        """``#print``-style query: show the declaration's kind, type, and
        (for definitions, theorems, and opaque constants) its value, all
        rendered by Lean's real pretty printer.

        >>> repl.inspect("Nat.add")
        'def Nat.add : Nat → Nat → Nat := ...'

        Unknown declarations raise :class:`RuntimeError`. Declarations
        created with :meth:`run_cmd` (``def``, ``axiom``, ...) are visible
        here.
        """
        return self._repl.inspect(name)

    # -- environment queries ------------------------------------------------
    def env_has_const(self, name: str) -> bool:
        return self._repl.env_has_const(name)


__all__ += ["Repl", "Goal"]
