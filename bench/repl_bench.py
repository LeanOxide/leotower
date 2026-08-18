"""Benchmark the Repl hot path (get_goals / get_goal_pp / run_tac).

Models the RL replay loop: set a goal, then repeatedly
(run_tac -> get_goals). Prints per-call medians in ms.
"""

import statistics
import time

from leotower import Repl


def median_ms(fn, n: int = 25) -> float:
    samples = []
    for _ in range(n):
        t0 = time.perf_counter()
        fn()
        samples.append((time.perf_counter() - t0) * 1e3)
    samples.sort()
    return statistics.median(samples)


def main() -> None:
    repl = Repl()
    s0 = repl.set_goal("∀ n m : Nat, n + m = m + n")
    s1 = repl.run_tac(s0, "intro n m")
    s2 = repl.run_tac(s1, "induction n")

    # warm up
    for _ in range(5):
        repl.get_goals(s2)
        repl.get_goal_pp(s2, 0)

    n_goals = repl.get_num_goals(s2)
    print(f"state s2 has {n_goals} goals")
    for i, g in enumerate(repl.get_goals(s2)):
        print(f"  goal[{i}] hyps={len(g.hyps)}: {g}")

    t_goals = median_ms(lambda: repl.get_goals(s2))
    t_pp = median_ms(lambda: repl.get_goal_pp(s2, 0))
    t_num = median_ms(lambda: repl.get_num_goals(s2))
    t_env = median_ms(lambda: repl.env_has_const("Nat.add"))

    print()
    print(f"get_goals (state with {n_goals} goals) : {t_goals:8.3f} ms")
    print(f"get_goal_pp (single goal)             : {t_pp:8.3f} ms")
    print(f"get_num_goals                          : {t_num:8.3f} ms")
    print(f"env_has_const                          : {t_env:8.3f} ms")

    # a state with more hypotheses, to stress the per-hyp cost
    repl2 = Repl()
    m0 = repl2.set_goal("∀ a b c : Nat, a + b + c = c + b + a")
    m1 = repl2.run_tac(m0, "intro a b c")
    for _ in range(5):
        repl2.get_goals(m1)
    t_multi = median_ms(lambda: repl2.get_goals(m1))
    nh = len(repl2.get_goals(m1)[0].hyps)
    print()
    print(f"get_goals (1 goal, {nh} hyps)          : {t_multi:8.3f} ms")


if __name__ == "__main__":
    main()
