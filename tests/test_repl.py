"""Repl tests: LeanDojo-compatible replay over the embedded Lean runtime."""

import sys

import pytest

from leotower import Repl, LeanError, TacticError

# Windows: constructing Repl() aborts the whole process (misaligned pointer
# dereference in leo3-ffi, exit 127, no Python traceback) — tracked in W-395.
# The Windows build + import + LeanSession paths are still exercised by
# tests/test_leotower.py; re-enable once W-395 lands.
pytestmark = pytest.mark.skipif(
    sys.platform == "win32",
    reason="Repl() aborts the process on Windows (W-395)",
)


ADD_COMM = "∀ n m : Nat, n + m = m + n"


def test_repl_init_and_env():
    repl = Repl()
    assert repl.env_has_const("Nat.add")
    assert repl.env_has_const("Nat")

def test_induction_with_clause_closes_proof():
    """`induction n with | zero => ... | succ ... => ...` is accepted and
    the branch naming works; a fully closing branch set ends at 0 goals.
    """
    repl = Repl()
    s0 = repl.set_goal(ADD_COMM)
    s1 = repl.run_tac(s0, "intro n m")
    s2 = repl.run_tac(
        s1,
        "induction n with | zero => simp only [Nat.zero_add, Nat.add_zero]"
        " | succ k ih => simp only [Nat.add_comm, Nat.add_succ]",
    )
    assert repl.get_num_goals(s2) == 0


def test_induction_with_unclosed_branch_raises():
    """A `with` branch that leaves its goal unsolved is rejected with the
    elaborator's unsolved-goals diagnostic — the system lean binary reports
    the same error at the end of the with-clause (verified against
    4.25.2). The session stays usable afterwards.
    """
    repl = Repl()
    s0 = repl.set_goal(ADD_COMM)
    s1 = repl.run_tac(s0, "intro n m")
    with pytest.raises(RuntimeError, match="tactic error"):
        repl.run_tac(
            s1,
            "induction n with | zero => simp only [Nat.zero_add]"
            " | succ k ih => simp only [Nat.add_comm]",
        )
    # the session survives the failed tactic: a valid one still applies
    s2 = repl.run_tac(s1, "induction n")
    assert repl.get_num_goals(s2) == 2


def test_set_goal_and_queries():
    repl = Repl()
    s0 = repl.set_goal(ADD_COMM)
    assert s0 == 0
    assert repl.get_num_goals(s0) == 1
    goals = repl.get_goals(s0)
    assert len(goals) == 1
    assert "Nat" in goals[0].ty
    pp = repl.get_goal_pp(s0)
    assert "⊢" in pp


def test_run_tac_steps():
    repl = Repl()
    s0 = repl.set_goal(ADD_COMM)
    s1 = repl.run_tac(s0, "intro n m")
    assert repl.get_num_goals(s1) == 1
    pp = repl.get_goal_pp(s1)
    # Real pretty printer groups same-type hypotheses on one line.
    assert "n m : Nat" in pp
    assert "n + m = m + n" in pp
    s2 = repl.run_tac(s1, "induction n")
    assert repl.get_num_goals(s2) == 2


def test_end_to_end_add_comm():
    repl = Repl()
    s0 = repl.set_goal(ADD_COMM)
    s1 = repl.run_tac(s0, "intro n m")
    s2 = repl.run_tac(s1, "induction n")
    assert repl.get_num_goals(s2) == 2
    # base case: 0 + m = m + 0 — closing goal 0 must PRESERVE the step goal
    s3 = repl.run_tac(s2, "simp only [Nat.zero_add, Nat.add_zero]", goal_idx=0)
    assert repl.get_num_goals(s3) == 1
    assert "n" in repl.get_goal_pp(s3, 0)
    # step case: n + 1 + m = m + (n + 1)
    s4 = repl.run_tac(s3, "simp only [Nat.add_comm, Nat.add_succ]")
    assert repl.get_num_goals(s4) == 0


def test_run_tac_goal_selection_arbitrary_order():
    repl = Repl()
    s0 = repl.set_goal(ADD_COMM)
    s1 = repl.run_tac(s0, "intro n m")
    s2 = repl.run_tac(s1, "induction n")
    assert repl.get_num_goals(s2) == 2
    # close the STEP goal first, then the base — goal selection is arbitrary
    t = repl.run_tac(s2, "simp only [Nat.add_comm, Nat.add_succ]", goal_idx=1)
    assert repl.get_num_goals(t) == 1
    assert "0 + m" in repl.get_goal_pp(t, 0)
    t2 = repl.run_tac(t, "simp only [Nat.zero_add, Nat.add_zero]")
    assert repl.get_num_goals(t2) == 0

def test_query_old_state_after_session_advances():
    """get_goals/get_goal_pp must work on any replay state, not just the
    session's latest. Advancing the session (run_tac on a descendant, closing
    goals, or branching onto an unrelated proof) must not invalidate
    re-querying an earlier state: goal lookups resolve the goal's metavariable
    through the session's meta state, which retains every mvar decl ever
    created, so old-state goals stay resolvable (and identically rendered)
    even after their proof has closed. This defends the state-isolation
    invariant that re-querying a state is stable under later session advances.
    """
    repl = Repl()
    s0 = repl.set_goal(ADD_COMM)
    s1 = repl.run_tac(s0, "intro n m")
    s2 = repl.run_tac(s1, "induction n")  # 2 goals: base + step
    # Snapshot the two goals on s2 BEFORE the session advances.
    base_pp = repl.get_goal_pp(s2, 0)
    step_pp = repl.get_goal_pp(s2, 1)
    assert "0 + m" in base_pp
    assert "n" in step_pp
    # Advance the session: close the base goal. The session's latest meta
    # state now branches off s2 and no longer contains s2's base-goal mvar.
    s3 = repl.run_tac(s2, "simp only [Nat.zero_add, Nat.add_zero]", goal_idx=0)
    assert repl.get_num_goals(s3) == 1
    # Re-query the OLD state s2 — must still see both goals and match the
    # snapshot, proving goal lookups are state-isolated.
    goals = repl.get_goals(s2)
    assert len(goals) == 2
    assert repl.get_goal_pp(s2, 0) == base_pp
    assert repl.get_goal_pp(s2, 1) == step_pp
    # And get_goals on the ADVANCED state s3 reflects only the step goal.
    goals3 = repl.get_goals(s3)
    assert len(goals3) == 1
    assert "n" in repl.get_goal_pp(s3, 0)


def test_run_tac_goal_idx_out_of_range():
    repl = Repl()
    s0 = repl.set_goal(ADD_COMM)
    s1 = repl.run_tac(s0, "intro n m")
    s2 = repl.run_tac(s1, "induction n")
    with pytest.raises(RuntimeError, match="no goal at index"):
        repl.run_tac(s2, "simp", goal_idx=5)


def test_invalid_tactic_raises_without_crashing():
    repl = Repl()
    s0 = repl.set_goal(ADD_COMM)
    with pytest.raises(RuntimeError, match="tactic parse error"):
        repl.run_tac(s0, "this is not a tactic !!!")
    # The session stays usable after the error.
    s1 = repl.run_tac(s0, "intro n m")
    assert repl.get_num_goals(s1) == 1


def test_run_cmd_validates_parse():
    repl = Repl()
    with pytest.raises(RuntimeError, match="command parse error"):
        repl.run_cmd("this is not a command @@@")


def test_run_cmd_executes_and_updates_env():
    repl = Repl()
    repl.run_cmd("def my_const : Nat := 42")
    assert repl.env_has_const("my_const")
    # Chained commands see earlier declarations.
    repl.run_cmd("theorem my_thm : my_const = my_const := rfl")
    assert repl.env_has_const("my_thm")
    # #check succeeds (information message, not an error).
    repl.run_cmd("#check Nat.add")


def test_run_cmd_failure_raises_and_session_survives():
    repl = Repl()
    with pytest.raises(RuntimeError, match="command failed"):
        repl.run_cmd("theorem bad : unknown_constant_xyz = 1 := rfl")
    # The session stays usable after the error.
    repl.run_cmd("axiom my_ax_ok : Nat")
    assert repl.env_has_const("my_ax_ok")
    s0 = repl.set_goal(ADD_COMM)
    s1 = repl.run_tac(s0, "intro n m")
    assert repl.get_num_goals(s1) == 1


def test_run_tac_on_closed_state_raises():
    repl = Repl()
    s0 = repl.set_goal("True")
    s1 = repl.run_tac(s0, "trivial")
    assert repl.get_num_goals(s1) == 0
    with pytest.raises(RuntimeError, match="no goal at index"):
        repl.run_tac(s1, "intro x")


def test_repl_loads_lean_file():
    import os

    path = os.path.join(os.path.dirname(__file__), "fixtures", "repl_demo.lean")
    repl = Repl(path)
    assert repl.env_has_const("demo_base")
    assert repl.env_has_const("demo_thm")
    # Commands can reference the file's definitions.
    repl.run_cmd("#check demo_base + demo_base")
    repl.run_cmd("theorem demo_cor : demo_base = demo_base := rfl")
    assert repl.env_has_const("demo_cor")
    # The session is usable for goals afterwards.
    s0 = repl.set_goal("∀ n : Nat, n + 0 = n")
    s1 = repl.run_tac(s0, "intro n")
    assert repl.get_num_goals(s1) == 1


def test_repl_loads_missing_file_raises():
    import pytest

    with pytest.raises(RuntimeError, match="cannot read"):
        Repl("tests/fixtures/does_not_exist.lean")


def test_run_tac_uses_locally_defined_constants():
    """Tactic elaboration must see constants added by run_cmd / file load."""
    repl = Repl()
    repl.run_cmd("def local_base : Nat := 21")
    s0 = repl.set_goal("local_base = 21")
    s1 = repl.run_tac(s0, "rfl")
    assert repl.get_num_goals(s1) == 0
    s0 = repl.set_goal("local_base + local_base = 42")
    s1 = repl.run_tac(s0, "native_decide")
    assert repl.get_num_goals(s1) == 0


def test_run_tac_rw_with_locally_defined_theorem():
    repl = Repl()
    repl.run_cmd("theorem add_zero_l (n : Nat) : n + 0 = n := Nat.add_zero n")
    s0 = repl.set_goal("∀ n : Nat, (n + 0) + 0 = n")
    s1 = repl.run_tac(s0, "intro n")
    s2 = repl.run_tac(s1, "rw [add_zero_l]")
    assert repl.get_num_goals(s2) == 0, [g.ty for g in repl.get_goals(s2)]


# ---------------------------------------------------------------------------
# P0 regression: tactic errors must be surfaced, not silently swallowed
# ---------------------------------------------------------------------------


def test_run_tac_type_error_raises():
    """`exact 42` against a proposition goal records an error diagnostic;
    the tactic returns Ok but the message must be surfaced as an exception."""
    repl = Repl()
    s0 = repl.set_goal("∀ n m : Nat, n + m = m + n")
    s1 = repl.run_tac(s0, "intro n m")
    with pytest.raises(RuntimeError, match="tactic error"):
        repl.run_tac(s1, "exact 42")
    # Session stays usable after the error.
    s3 = repl.run_tac(s1, "exact Nat.add_comm n m")
    assert repl.get_num_goals(s3) == 0


def test_run_tac_unknown_identifier_raises():
    """`rw [nonexistent_lemma]` errors with the unknown identifier message."""
    repl = Repl()
    s0 = repl.run_tac(repl.set_goal("∀ n m : Nat, n + m = m + n"), "intro n m")
    with pytest.raises(RuntimeError, match="tactic error"):
        repl.run_tac(s0, "rw [nonexistent_lemma]")


def test_run_tac_valid_still_works():
    """Valid tactics are unaffected by the error scan."""
    repl = Repl()
    s0 = repl.run_tac(repl.set_goal("∀ n m : Nat, n + m = m + n"), "intro n m")
    s1 = repl.run_tac(s0, "exact Nat.add_comm n m")
    assert repl.get_num_goals(s1) == 0


# ---------------------------------------------------------------------------
# P1 regression: dotted module names + LEAN_PATH search path support
# ---------------------------------------------------------------------------


def test_repl_imports_dotted_modules(tmp_path):
    """Dot-separated module names must resolve to hierarchical Lean names
    (regression: `basic.MyThm` failed with `unknown module prefix` because
    the name was built as a flat component instead of a hierarchy)."""
    import os
    import subprocess

    lean = os.environ.get(
        "LEAN_BIN", "/home/ljm/.lemma/toolchains/v4.25.2-linux/bin/lean"
    )
    if not os.path.exists(lean):
        pytest.skip("lean toolchain not found")
    src_dir = tmp_path / "basic"
    src_dir.mkdir()
    (src_dir / "MyThm.lean").write_text("theorem my_thm : 1 + 1 = 2 := by rfl\n")
    lib = tmp_path / "build" / "lib" / "lean" / "basic"
    lib.mkdir(parents=True)
    subprocess.run(
        [lean, "-R", str(tmp_path),
         "-o", str(tmp_path / "build" / "lib" / "lean" / "basic" / "MyThm.olean"),
         str(src_dir / "MyThm.lean")],
        check=True,
        capture_output=True,
    )
    os.environ["LEAN_PATH"] = str(tmp_path / "build" / "lib" / "lean")
    try:
        repl = Repl("basic.MyThm")
        assert repl.env_has_const("my_thm")
    finally:
        os.environ.pop("LEAN_PATH", None)


def test_repl_import_missing_module_raises():
    with pytest.raises(RuntimeError, match="unknown module prefix"):
        Repl("No.Such.Module")


def test_repl_import_via_lean_path(tmp_path):
    """Modules compiled into a lake-style search path (like Mathlib) must be
    importable via LEAN_PATH; missing ones must fail loudly."""
    import os
    import subprocess

    lean = os.environ.get(
        "LEAN_BIN", "/home/ljm/.lemma/toolchains/v4.25.2-linux/bin/lean"
    )
    if not os.path.exists(lean):
        pytest.skip("lean toolchain not found")
    # Build a tiny "lake-style" module: `basic/MyThm.lean` -> basic.MyThm.olean
    src_dir = tmp_path / "basic"
    src_dir.mkdir()
    (src_dir / "MyThm.lean").write_text(
        "theorem my_thm : 1 + 1 = 2 := by rfl\n"
    )
    lib = tmp_path / "build" / "lib" / "lean" / "basic"
    lib.mkdir(parents=True)
    subprocess.run(
        [lean, "-R", str(tmp_path),
         "-o", str(tmp_path / "build" / "lib" / "lean" / "basic" / "MyThm.olean"),
         str(src_dir / "MyThm.lean")],
        check=True,
        capture_output=True,
    )
    os.environ["LEAN_PATH"] = str(tmp_path / "build" / "lib" / "lean")
    try:
        repl = Repl("basic.MyThm")
        repl.run_cmd("#check my_thm")  # no exception => symbol resolved
        assert repl.env_has_const("my_thm")
    finally:
        os.environ.pop("LEAN_PATH", None)

# ---------------------------------------------------------------------------
# Mathlib integration: mathlib-level tactics via a lake-built LEAN_PATH
# ---------------------------------------------------------------------------


def _mathlib_lean_path():
    """Return the LEAN_PATH for a locally built mathlib4 checkout, or None.

    Looks for the lake v5 build layout (``<root>/.lake/build/lib/lean``) in
    the sibling ``mathlib4`` checkout; the path is reconstructed from the
    package directories so the test needs no ``lake`` invocation.
    """
    import os
    from pathlib import Path

    candidates = [
        Path(__file__).resolve().parent.parent.parent / "mathlib4",
        Path.home() / "mathlib4",
    ]
    for root in candidates:
        main_olean = root / ".lake" / "build" / "lib" / "lean" / "Mathlib.olean"
        if main_olean.exists():
            entries = []
            packages = root / ".lake" / "packages"
            if packages.is_dir():
                for pkg in sorted(packages.iterdir()):
                    p = pkg / ".lake" / "build" / "lib" / "lean"
                    if p.is_dir():
                        entries.append(str(p))
            entries.append(str(root / ".lake" / "build" / "lib" / "lean"))
            return os.pathsep.join(entries)
    return None


def test_repl_mathlib_import_and_tactics():
    """Mathlib tactics survive a preceding core-Lean Repl in one process.

    This is the regression for Leo3's initializer-execution flag: Lean's
    ``withImporting`` resets that process-global flag after each import, so
    Leo3 must re-enable it before every independent Repl environment import.
    Skipped when no local mathlib4 build exists.
    """
    import os

    lean_path = _mathlib_lean_path()
    if lean_path is None:
        pytest.skip("no locally built mathlib4 (expected: ../mathlib4/.lake/build)")
    old = os.environ.get("LEAN_PATH")
    os.environ["LEAN_PATH"] = lean_path
    try:
        # Explicitly exercise the formerly poisonous order.
        Repl()
        repl = Repl("Mathlib")

        s0 = repl.set_goal("∀ n m : Nat, n + m = m + n")
        s1 = repl.run_tac(repl.run_tac(s0, "intro n m"), "linarith")
        assert repl.get_num_goals(s1) == 0

        s0 = repl.set_goal("∀ a b c : Nat, a * (b + c) = a * b + a * c")
        s1 = repl.run_tac(repl.run_tac(s0, "intro a b c"), "ring")
        assert repl.get_num_goals(s1) == 0

        s0 = repl.set_goal("2 + 2 = 4")
        s1 = repl.run_tac(s0, "norm_num")
        assert repl.get_num_goals(s1) == 0
    finally:
        if old is None:
            os.environ.pop("LEAN_PATH", None)
        else:
            os.environ["LEAN_PATH"] = old


def test_run_tacs_applies_sequence():
    """run_tacs applies a tactic sequence in order, one call end to end."""
    repl = Repl()
    s0 = repl.set_goal(ADD_COMM)
    # intro -> induction -> close base -> close step, all in a single call.
    s_final = repl.run_tacs(
        s0,
        ["intro n m", "induction n",
         "simp only [Nat.zero_add, Nat.add_zero]",
         "simp only [Nat.add_comm, Nat.add_succ]"],
    )
    assert repl.get_num_goals(s_final) == 0


def test_run_tacs_empty_returns_same_state():
    repl = Repl()
    s0 = repl.set_goal(ADD_COMM)
    assert repl.run_tacs(s0, []) == s0


def test_run_tacs_failure_raises_and_session_survives():
    """A failing tactic in the middle raises RuntimeError; the states that
    were produced before the failure are still queryable."""
    repl = Repl()
    s0 = repl.set_goal(ADD_COMM)
    s1 = repl.run_tacs(s0, ["intro n m"])
    assert repl.get_num_goals(s1) == 1
    with pytest.raises(RuntimeError):
        # "intro n m" already introduced both vars; re-introducing fails.
        repl.run_tacs(s1, ["intro n m", "rfl"])
    # The session stays usable after the error.
    s2 = repl.run_tac(s1, "induction n")
    assert repl.get_num_goals(s2) == 2


# ---------------------------------------------------------------------------
# Non-raising variants: try_run_tac / try_run_tacs (proof-search / RL loops)
# ---------------------------------------------------------------------------


def test_try_run_tac_success():
    """On success, try_run_tac returns (new_state, True)."""
    repl = Repl()
    s0 = repl.set_goal(ADD_COMM)
    s1, ok = repl.try_run_tac(s0, "intro n m")
    assert ok is True
    assert s1 != s0
    assert repl.get_num_goals(s1) == 1


def test_try_run_tac_failure_returns_source_state_no_raise():
    """A failing tactic returns (source_state, False) and does not raise.
    No new state is appended, and the session stays usable afterwards."""
    repl = Repl()
    s0 = repl.set_goal(ADD_COMM)
    s, ok = repl.try_run_tac(s0, "rw [nonexistent_lemma]")
    assert ok is False
    assert s == s0
    # The failed attempt did not append a state.
    assert repl.num_states() == 1
    # The session is still usable: run_tac and get_goals work.
    s1 = repl.run_tac(s0, "intro n m")
    assert repl.get_num_goals(s1) == 1


def test_try_run_tac_goal_idx_out_of_range():
    repl = Repl()
    s0 = repl.set_goal(ADD_COMM)
    s, ok = repl.try_run_tac(s0, "simp", goal_idx=5)
    assert ok is False
    assert s == s0


def test_try_run_tac_unknown_state():
    """An out-of-range state id returns (state, False) instead of raising."""
    repl = Repl()
    repl.set_goal(ADD_COMM)
    s, ok = repl.try_run_tac(99, "intro n m")
    assert ok is False
    assert s == 99


def test_try_run_tac_success_matches_run_tac():
    """On success, the try_ variant advances the proof exactly like run_tac:
    the resulting state has the same remaining goal. Each goal pp is
    snapshot while its state is the session's latest (re-querying a sibling
    branch after the session advances on another is a pre-existing
    limitation, covered separately)."""
    repl = Repl()
    s0 = repl.set_goal(ADD_COMM)
    s_ran = repl.run_tac(s0, "intro n m")
    ran_pp = repl.get_goal_pp(s_ran)  # snapshot while s_ran is the latest
    s_try, ok = repl.try_run_tac(s0, "intro n m")
    assert ok is True
    assert repl.get_num_goals(s_try) == 1
    try_pp = repl.get_goal_pp(s_try)
    # Both branches from s0 with "intro n m" render the same remaining goal.
    assert "n m : Nat" in ran_pp and "n m : Nat" in try_pp
    assert "n + m = m + n" in ran_pp and "n + m = m + n" in try_pp


def test_try_run_tacs_applies_sequence():
    """try_run_tacs applies the sequence and returns (final_state, True)."""
    repl = Repl()
    s0 = repl.set_goal(ADD_COMM)
    s_final, ok = repl.try_run_tacs(
        s0,
        ["intro n m", "induction n",
         "simp only [Nat.zero_add, Nat.add_zero]",
         "simp only [Nat.add_comm, Nat.add_succ]"],
    )
    assert ok is True
    assert repl.get_num_goals(s_final) == 0


def test_try_run_tacs_mid_sequence_failure():
    """A failing tactic midway returns (last_successful_state, False) without
    raising. The state after the last successful tactic stays queryable and
    the session stays usable."""
    repl = Repl()
    s0 = repl.set_goal(ADD_COMM)
    # "intro n m" succeeds; the next tactic fails on an unknown identifier.
    s, ok = repl.try_run_tacs(s0, ["intro n m", "rw [nonexistent_lemma]", "rfl"])
    assert ok is False
    # The first tactic succeeded, so the returned state is the one after it.
    assert s != s0
    assert repl.get_num_goals(s) == 1
    # The session is still usable after the failure.
    s2 = repl.run_tac(s, "induction n")
    assert repl.get_num_goals(s2) == 2


def test_try_run_tacs_empty_returns_state_true():
    repl = Repl()
    s0 = repl.set_goal(ADD_COMM)
    s, ok = repl.try_run_tacs(s0, [])
    assert ok is True
    assert s == s0


# ---------------------------------------------------------------------------
# Query commands: check (#check), inspect (#print), num_states
# ---------------------------------------------------------------------------


def test_check_constant_root_context():
    repl = Repl()
    assert repl.check("Nat.add") == "Nat.add : Nat → Nat → Nat"


def test_check_polymorphic_constant_uses_declared_type():
    """A bare polymorphic constant prints `#check`-style (implicit and
    universe arguments remain binders); a `have`-based elaboration would
    reject it for unsynthesizable implicits."""
    repl = Repl()
    assert repl.check("List.map") == (
        "List.map : {α : Type u_1} → {β : Type u_2} → (α → β) → List α → List β"
    )


def test_check_non_constant_in_local_context():
    repl = Repl()
    s0 = repl.set_goal("∀ n : Nat, n = n")
    s1 = repl.run_tac(s0, "intro n")
    assert repl.check("n", state=s1) == "n : Nat"
    assert repl.check("n + 1", state=s1) == "n + 1 : Nat"


def test_check_sees_run_cmd_constants():
    """The constant path must see declarations added via run_cmd."""
    repl = Repl()
    repl.run_cmd("def my_leotower_const : Nat := 5")
    assert repl.check("my_leotower_const") == "my_leotower_const : Nat"


def test_check_unknown_identifier_raises():
    repl = Repl()
    with pytest.raises(RuntimeError, match="Unknown identifier"):
        repl.check("no_such_decl_xyz")


def test_check_out_of_scope_local_raises():
    """Local hypotheses are not visible from the root context, and the
    session is left intact."""
    repl = Repl()
    s0 = repl.set_goal("∀ n : Nat, n = n")
    s1 = repl.run_tac(s0, "intro n")
    with pytest.raises(RuntimeError, match="Unknown identifier"):
        repl.check("n")
    assert repl.get_num_goals(s1) == 1


def test_check_unknown_state_raises_with_range():
    repl = Repl()
    repl.set_goal(ADD_COMM)
    with pytest.raises(RuntimeError, match=r"unknown state 99 \(valid states: 0\.\.=0\)"):
        repl.check("Nat.add", state=99)


def test_check_on_closed_state_raises():
    repl = Repl()
    s0 = repl.set_goal("∀ n : Nat, n = n")
    s1 = repl.run_tac(s0, "intro n")
    s2 = repl.run_tac(s1, "exact rfl")
    with pytest.raises(RuntimeError, match=r"no goal at index 0 in state 2 \(state has 0 goals\)"):
        repl.check("n", state=s2)


def test_check_bad_goal_idx_raises():
    repl = Repl()
    s0 = repl.set_goal(ADD_COMM)
    with pytest.raises(RuntimeError, match=r"no goal at index 3 in state 0"):
        repl.check("Nat.add", state=s0, goal_idx=3)


def test_check_session_not_modified():
    """check must not consume or alter replay states."""
    repl = Repl()
    s0 = repl.set_goal(ADD_COMM)
    s1 = repl.run_tac(s0, "intro n")
    repl.check("n", state=s1)
    repl.check("List.map")
    assert repl.get_num_goals(s1) == 1
    s2 = repl.run_tac(s1, "exact fun m => Nat.add_comm n m")
    assert repl.get_num_goals(s2) == 0


def test_check_local_shadow_of_global_constant():
    """A local fvar shadowing a global constant must win: the name
    resolves to the local declaration, not the global one."""
    repl = Repl()
    s = repl.set_goal("∀ List : Nat, List = List")
    s = repl.run_tac(s, "intro List")
    assert repl.check("List", state=s) == "List : Nat"


def test_check_local_shadow_of_Nat():
    """Shadowing a core constant (here `Nat`) resolves to the local; the
    local's type is the global `Nat` type, disambiguated as `_root_.Nat`."""
    repl = Repl()
    s = repl.set_goal("∀ Nat : Nat, True")
    s = repl.run_tac(s, "intro Nat")
    assert repl.check("Nat", state=s) == "Nat : _root_.Nat"
def test_check_local_prefix_shadow_of_qualified_name():
    """A local `List` also shadows the prefix of `List.map`: the
    constant fast path is skipped and Lean's own error is surfaced."""
    repl = Repl()
    s = repl.set_goal("∀ List : Nat, List = List")
    s = repl.run_tac(s, "intro List")
    with pytest.raises(RuntimeError):
        repl.check("List.map", state=s)


def test_check_unshadowed_constant_still_uses_declared_type():
    """The fast path must not regress for unshadowed names, even in a
    local context that merely contains other hypotheses."""
    repl = Repl()
    s0 = repl.set_goal("∀ n : Nat, n = n")
    s1 = repl.run_tac(s0, "intro n")
    assert repl.check("List.map", state=s1) == (
        "List.map : {α : Type u_1} → {β : Type u_2} → (α → β) → List α → List β"
    )


def test_inspect_definition():
    repl = Repl()
    out = repl.inspect("Nat.add")
    assert out.startswith("def Nat.add : Nat → Nat → Nat")
    assert ":=" in out


def test_inspect_polymorphic_constant():
    repl = Repl()
    out = repl.inspect("List.map")
    assert out.startswith("def List.map")
    assert "List α → List β" in out


def test_inspect_axiom_has_no_value():
    repl = Repl()
    repl.run_cmd("axiom my_leotower_ax : Nat")
    out = repl.inspect("my_leotower_ax")
    assert out == "axiom my_leotower_ax : Nat"


def test_inspect_unknown_raises():
    repl = Repl()
    with pytest.raises(RuntimeError, match="unknown constant"):
        repl.inspect("no_such_decl_xyz")


def test_num_states_counts():
    repl = Repl()
    assert repl.num_states() == 0
    s0 = repl.set_goal(ADD_COMM)
    assert repl.num_states() == 1
    s1 = repl.run_tac(s0, "intro n")
    assert repl.num_states() == 2


# ============================================================================
# Exception hierarchy: LeanError / TacticError
# ============================================================================


def test_exception_hierarchy():
    """TacticError refines LeanError; both refine RuntimeError so existing
    ``except RuntimeError`` handlers keep working (backward compatibility)."""
    assert issubclass(LeanError, RuntimeError)
    assert issubclass(TacticError, LeanError)


def test_tactic_failures_raise_tactic_error():
    """Every tactic-failure path raises TacticError with the original
    message and cause preserved."""
    repl = Repl()
    s0 = repl.set_goal(ADD_COMM)
    # Type error.
    with pytest.raises(TacticError, match="tactic error") as excinfo:
        repl.run_tac(s0, "exact 42")
    # The original message and the underlying cause are preserved.
    assert isinstance(excinfo.value.__cause__, RuntimeError)
    # Parse error — a bare ``except RuntimeError`` still catches it
    # (backward compatibility) and the concrete type is TacticError.
    with pytest.raises(RuntimeError, match="tactic parse error") as excinfo:
        repl.run_tac(s0, "this is not a tactic !!!")
    assert isinstance(excinfo.value, TacticError)
    # Unknown state.
    with pytest.raises(TacticError, match="unknown state"):
        repl.run_tac(99, "intro n")
    # run_tacs propagates the TacticError of the failing element.
    s1 = repl.run_tac(s0, "intro n m")
    with pytest.raises(TacticError):
        # "intro n m" already introduced both vars; re-introducing fails.
        repl.run_tacs(s1, ["intro n m", "rfl"])


def test_non_tactic_failures_raise_lean_error():
    """set_goal / run_cmd / check / inspect failures raise LeanError."""
    repl = Repl()
    with pytest.raises(LeanError):
        repl.set_goal("this is not a term @@@")
    with pytest.raises(LeanError, match="command parse error"):
        repl.run_cmd("this is not a command @@@")
    with pytest.raises(LeanError, match="Unknown identifier"):
        repl.check("no_such_decl_xyz")
    with pytest.raises(LeanError, match="unknown constant"):
        repl.inspect("no_such_decl_xyz")


def test_every_error_is_caught_by_except_runtime_error():
    """Backward compatibility across the whole hierarchy: each wrapped
    failure is still caught by a plain ``except RuntimeError`` handler."""
    repl = Repl()
    s0 = repl.set_goal(ADD_COMM)
    for call in (
        lambda: repl.run_tac(s0, "this is not a tactic !!!"),
        lambda: repl.run_tacs(s0, ["this is not a tactic !!!"]),
        lambda: repl.set_goal("this is not a term @@@"),
        lambda: repl.run_cmd("this is not a command @@"),
        lambda: repl.check("no_such_decl_xyz"),
        lambda: repl.inspect("no_such_decl_xyz"),
    ):
        with pytest.raises(RuntimeError):
            call()
