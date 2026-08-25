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

    def __str__(self):
        """Standard goal display: one ``name : type`` line per hypothesis
        followed by ``⊢ ty`` — the same ``hyps ⊢ type`` shape as
        :meth:`Repl.get_goal_pp` (which renders via Lean's pretty printer,
        e.g. grouping same-type hypotheses).  With no hypotheses the
        string is just ``⊢ ty``.
        """
        lines = [f"{name} : {ty}" for name, ty in self.hyps]
        lines.append(f"⊢ {self.ty}")
        return "\n".join(lines)

    def __repr__(self):
        return f"Goal({self.hyps!r} ⊢ {self.ty})"


class LeanError(RuntimeError):
    """Base class for leotower Lean-operation errors.

    A subclass of :class:`RuntimeError`, so existing ``except RuntimeError``
    handlers keep working unchanged.  Raised by :class:`Repl` operations
    that fail outside of tactic application: :meth:`Repl.set_goal`,
    :meth:`Repl.check`, :meth:`Repl.inspect`, and :meth:`Repl.run_cmd`.
    """


class TacticError(LeanError):
    """A tactic failed to parse, elaborate, or apply; the session and the
    replay state stay usable.
    """


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
        try:
            return self._repl.set_goal(type_str)
        except RuntimeError as e:
            raise LeanError(str(e)) from e

    def run_tac(self, state: int, tactic: str, goal_idx: int = 0) -> int:
        """Apply ``tactic`` to the ``goal_idx``-th goal of ``state`` (default
        0); returns the new state id.  Multi-goal states (from ``induction``,
        ``split``, ``cases``) keep their unworked goals in the new state, so
        a proof can advance goal by goal in any order.  Invalid tactics
        raise :class:`TacticError` (the interpreter and the replay state
        stay intact)."""
        try:
            return self._repl.run_tac(state, tactic, goal_idx)
        except RuntimeError as e:
            raise TacticError(str(e)) from e

    def try_run_tac(self, state: int, tactic: str, goal_idx: int = 0) -> "tuple[int, bool]":
        """Non-raising variant of :meth:`run_tac`: returns
        ``(state_id, success)`` instead of raising :class:`TacticError`.

        On success the new state id and ``True`` are returned. On failure
        (unknown state, out-of-range goal, or tactic parse/elaboration/run
        error) the source ``state`` id and ``False`` are returned, and no
        new state is appended — the session and the replay state stay
        usable. This is the core idiom for proof-search / RL loops (try a
        tactic, learn whether it succeeded):

        >>> s2, ok = repl.try_run_tac(s1, "simp")
        """
        return self._repl.try_run_tac(state, tactic, goal_idx)

    def run_cmd(self, cmd: str) -> None:
        """Execute a Lean command in the current environment.

        The command is parsed with Lean's real parser and elaborated by the
        embedded frontend (``Lean.Elab.Command.elabCommandTopLevel``); the
        resulting environment is installed for subsequent calls. Commands
        that fail elaboration raise :class:`LeanError` (the session stays
        usable). Commands do not create replay states and return nothing —
        use :meth:`inspect` / :meth:`check` for declaration and term
        queries, and only run environment-mutating commands here.
        """
        try:
            self._repl.run_cmd(cmd)
        except RuntimeError as e:
            raise LeanError(str(e)) from e

    # -- goal queries -------------------------------------------------------
    def get_num_goals(self, state: int) -> int:
        return self._repl.get_num_goals(state)

    def get_goals(self, state: int):
        raw = self._repl.get_goals(state)
        return [Goal(g.hyps, g.ty, g.mvar) for g in raw]

    def get_goal_pp(self, state: int, goal_idx: int = 0) -> str:
        return self._repl.get_goal_pp(state, goal_idx)

    def get_state_pp(self, state: int) -> str:
        """Pretty-print every goal of ``state`` in one string.

        With 0 goals returns ``"no goals"``. With 1 goal returns exactly
        :meth:`get_goal_pp` output for goal 0. With N goals the per-goal
        pretty prints are numbered and joined with a blank line::

            goal[0]:
            <pp0>

            goal[1]:
            <pp1>
        """
        n = self.get_num_goals(state)
        if n == 0:
            return "no goals"
        if n == 1:
            return self.get_goal_pp(state, 0)
        return "\n\n".join(
            f"goal[{i}]:\n{self.get_goal_pp(state, i)}" for i in range(n)
        )

    def run_tacs(self, state: int, tactics: "list[str]", goal_idx: int = 0) -> int:
        """Apply a sequence of tactics in order to the ``goal_idx``-th goal,
        starting from ``state``; returns the final state id.  This is the
        replay/RL loop idiom — apply ``[t1, t2, ...]`` without threading
        intermediate state ids by hand.  Tactics are applied left to right;
        the first one to fail raises :class:`TacticError` and the returned
        state is that of the last successful tactic (the session stays
        usable).  If ``tactics`` is empty, ``state`` is returned unchanged.
        """
        cur = state
        for tac in tactics:
            cur = self.run_tac(cur, tac, goal_idx)
        return cur

    def try_run_tacs(self, state: int, tactics: "list[str]", goal_idx: int = 0) -> "tuple[int, bool]":
        """Non-raising variant of :meth:`run_tacs`: apply a sequence of
        tactics in order to the ``goal_idx``-th goal, starting from
        ``state``, and return ``(state_id, success)`` instead of raising
        :class:`TacticError`.

        If every tactic succeeds, ``(final_state, True)`` is returned. If
        one fails midway, the state after the last successful tactic and
        ``False`` are returned — the states produced before the failure
        stay queryable and the session stays usable. If ``tactics`` is
        empty, ``(state, True)`` is returned unchanged.
        """
        cur = state
        for tac in tactics:
            cur, ok = self.try_run_tac(cur, tac, goal_idx)
            if not ok:
                return cur, False
        return cur, True

    # -- replay introspection -----------------------------------------------
    def num_states(self) -> int:
        """Number of replay states created so far (``0`` before the first
        :meth:`set_goal`).  Valid state ids are ``0..num_states()``
        (half-open — the highest valid id is ``num_states() - 1``)."""
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

        Name resolution follows Lean: a local hypothesis that shadows
        the name — including a prefix shadow of a qualified name (a
        local ``List`` also shadows ``List.map``) — resolves to the
        local declaration, not the global constant.

        Names are resolved at the meta level: use fully qualified names
        (command-level scopes such as ``open`` do not apply). Elaboration
        failures (unknown identifiers, type errors) raise
        :class:`LeanError` with Lean's error message; the replay session
        is not modified.

        >>> repl.check("Nat.add")
        'Nat.add : Nat → Nat → Nat'
        """
        try:
            return self._repl.check(term, state, goal_idx)
        except RuntimeError as e:
            raise LeanError(str(e)) from e

    def inspect(self, name: str) -> str:
        """``#print``-style query: show the declaration's kind, type, and
        (for definitions, theorems, and opaque constants) its value, all
        rendered by Lean's real pretty printer.

        >>> repl.inspect("Nat.add")
        'def Nat.add : Nat → Nat → Nat := ...'

        Unknown declarations raise :class:`LeanError`. Declarations
        created with :meth:`run_cmd` (``def``, ``axiom``, ...) are visible
        here.
        """
        try:
            return self._repl.inspect(name)
        except RuntimeError as e:
            raise LeanError(str(e)) from e

    # -- environment queries ------------------------------------------------
    def env_has_const(self, name: str) -> bool:
        return self._repl.env_has_const(name)


__all__ += ["Repl", "Goal", "LeanError", "TacticError"]
