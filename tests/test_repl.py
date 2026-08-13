"""Repl tests: LeanDojo-compatible replay over the embedded Lean runtime."""

import pytest

from leotower import Repl


ADD_COMM = "∀ n m : Nat, n + m = m + n"


def test_repl_init_and_env():
    repl = Repl()
    assert repl.env_has_const("Nat.add")
    assert repl.env_has_const("Nat")


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
