"""Scale get_goals vs get_goal_pp against hypothesis count (release mode).

For each N, build `∀ x_0 ... x_{N-1} : Nat, True`, intro all N, then time:
  - get_goals(s)      : structured (hyps, ty) per goal
  - get_goal_pp(s,0)  : flat string via ppGoal

A CONSTANT gap across N -> the extra get_mvar_decl worker trip dominates.
A LINEAR gap across N  -> per-expr delaboration in pp_exprs dominates.
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


def build_state(n_hyps: int) -> "tuple[Repl, int]":
    # `∀ x_0 x_1 ... x_{N-1} : Nat, True`
    if n_hyps == 0:
        goal = "True"
    else:
        goal = "∀ " + " ".join(f"x_{i}" for i in range(n_hyps)) + " : Nat, True"
    repl = Repl()
    s0 = repl.set_goal(goal)
    if n_hyps == 0:
        s = s0
    else:
        s = repl.run_tac(s0, "intro " + " ".join(f"x_{i}" for i in range(n_hyps)))
    g = repl.get_goals(s)[0]
    assert len(g.hyps) == n_hyps, (len(g.hyps), n_hyps)
    return repl, s


def main() -> None:
    print(f"{'N':>4} | {'get_goals ms':>12} | {'get_goal_pp ms':>14} | {'gap x':>6}")
    print("-" * 52)
    for n in (0, 1, 2, 5, 10, 20, 40, 80):
        repl, s = build_state(n)
        for _ in range(5):
            repl.get_goals(s)
            repl.get_goal_pp(s, 0)
        tg = median_ms(lambda: repl.get_goals(s))
        tp = median_ms(lambda: repl.get_goal_pp(s, 0))
        gap = (tg / tp) if tp > 0 else float("inf")
        print(f"{n:>4} | {tg:>12.3f} | {tp:>14.3f} | {gap:>6.2f}")


if __name__ == "__main__":
    main()
