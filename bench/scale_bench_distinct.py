"""Scale get_goals / get_goal_pp with DISTINCT-type hyps (release mode).

Unlike scale_bench.py (all hyps type `Nat`, where consecutive-equal-type dedup
collapses N+1 ppExpr calls to ~2), this builds a goal whose hypotheses all have
*distinct* types: `∀ (x_0 : Fin 0) (x_1 : Fin 1) ... (x_{N-1} : Fin (N-1)), True`.

If get_goals stays ~flat/linear in N, the per-ppExpr cost is O(1) and the
consecutive-equal-type dedup is the complete fix. If get_goals grows superlinearly
(quadratically), a single top-level ppExpr call is O(N) in lctx size and the
distinct-type general case still needs a single-pass (shared-context) delaboration.
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
    # `∀ (x_0 : Fin 0) ... (x_{N-1} : Fin (N-1)), True`  (all distinct types)
    if n_hyps == 0:
        goal = "True"
    else:
        binders = " ".join(f"(x_{i} : Fin {i})" for i in range(n_hyps))
        goal = f"∀ {binders}, True"
    repl = Repl()
    s0 = repl.set_goal(goal)
    if n_hyps == 0:
        s = s0
    else:
        s = repl.run_tac(s0, "intro " + " ".join(f"x_{i}" for i in range(n_hyps)))
    g = repl.get_goals(s)[0]
    assert len(g.hyps) == n_hyps, (len(g.hyps), n_hyps)
    # sanity: types really are distinct
    types = [h[1] for h in g.hyps]
    assert len(set(types)) == n_hyps, "expected all-distinct hyp types"
    return repl, s


def main() -> None:
    print(f"{'N':>4} | {'get_goals ms':>13} | {'get_goal_pp ms':>14} | {'gap x':>6}")
    print("-" * 52)
    for n in [0, 1, 5, 10, 20, 40, 80]:
        repl, s = build_state(n)
        a = median_ms(lambda: repl.get_goals(s))
        b = median_ms(lambda: repl.get_goal_pp(s, 0))
        gap = a / b if b > 0 else float("nan")
        print(f"{n:>4} | {a:>13.3f} | {b:>14.3f} | {gap:>6.2f}")


if __name__ == "__main__":
    main()
