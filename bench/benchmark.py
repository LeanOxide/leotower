"""Benchmark: embedded Lean (leo3-py) vs one process per call (lean --run).

The subprocess mode mirrors how LeanDojo-style pipelines talk to Lean today:
one Lean process per request.  The embedded mode keeps the runtime in-process.
"""

import os
import statistics
import subprocess
import tempfile
import time

import leo3_py

N_EMBEDDED = 20_000
N_SUBPROCESS = 20

SRC = "def main : IO Unit := IO.println (toString (Nat.add {i} 1))\n"


def bench_embedded(n: int) -> float:
    with leo3_py.with_lean() as lean:
        t0 = time.perf_counter()
        for i in range(n):
            assert lean.nat_add(i, 1) == i + 1
        return time.perf_counter() - t0


def one_subprocess_call(i: int) -> None:
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as f:
        f.write(SRC.format(i=i))
        path = f.name
    try:
        subprocess.run(
            ["lean", "--run", path], capture_output=True, check=True
        )
    finally:
        os.unlink(path)


def bench_subprocess(n: int) -> float:
    t0 = time.perf_counter()
    for i in range(n):
        one_subprocess_call(i)
    return time.perf_counter() - t0


def main() -> None:
    # Note on the comparison: the embedded mode measures a *hot* call on an
    # already-initialized runtime (the steady-state cost of one step in a
    # proof-search/RL loop); the subprocess mode measures one cold
    # process-per-request (Lean startup + Std import + evaluation), which is
    # what process-per-request pipelines pay for every single step.
    t_emb = bench_embedded(N_EMBEDDED)
    per_emb = t_emb / N_EMBEDDED * 1e6

    # warm-up for subprocess (filesystem/page cache)
    one_subprocess_call(0)
    t_sub = bench_subprocess(N_SUBPROCESS)
    per_sub = t_sub / N_SUBPROCESS * 1e3

    print(f"embedded : {N_EMBEDDED} calls in {t_emb:.3f}s  -> {per_emb:.1f} us/call")
    print(f"subprocess: {N_SUBPROCESS} calls in {t_sub:.3f}s  -> {per_sub:.2f} ms/call")
    print(f"speedup  : {per_sub * 1e3 / per_emb:.0f}x")


if __name__ == "__main__":
    main()
