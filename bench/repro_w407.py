#!/usr/bin/env python3
"""Repro for W-407: repeated `Repl()` construction in one process.

Before the W-407 fix stack (S1: per-command heartbeat reset, S2: the leo3
`free_regions` API, S3: `Repl` drop freeing the environment's import regions),
each `Repl()` permanently leaked ~1.4-1.6 GB of compacted import regions
(Bug A), and once enough had been constructed in one process a trivial
`set_goal` tripped a spurious `maxHeartbeats` timeout (Bug B).

Usage:
    python repro_w407.py <iterations> [repl-per-iter]

Each iteration constructs `repl-per-iter` fresh `Repl()` instances (default
module "Lean", so each re-imports and re-elaborates the whole Lean module),
runs one trivial `set_goal`, drops them and forces a GC, then samples the
process RSS. Per-iteration import/goal timing and RSS are printed, and the run
FAILs (exit 1) if:

  - a Lean exception / `maxHeartbeats` / OOM is raised, or
  - RSS grows by more than 512 MB from the first to the last sampled
    iteration (the leak signature is ~+3 GB/iter at 2 Repl/iter).

The pass condition is a flat ~200-500 MB RSS across all iterations with no
exception — i.e. the region buffer is released on drop and the heartbeat
counter no longer accumulates across commands.
"""

import gc
import sys
import time


def current_rss_mb() -> float:
    """Current process resident set size in MB (Linux: VmRSS)."""
    try:
        with open("/proc/self/status") as f:
            for line in f:
                if line.startswith("VmRSS:"):
                    return int(line.split()[1]) / 1024.0
    except OSError:
        pass
    # Fallback (high-water mark, e.g. non-Linux).
    import resource

    return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024.0


def main(argv: list[str]) -> int:
    iterations = int(argv[0])
    per_iter = int(argv[1]) if len(argv) > 1 else 2
    max_growth_mb = 512.0

    from leotower import Repl

    first = None
    last = None
    peak = 0.0
    try:
        for i in range(iterations):
            t0 = time.perf_counter()
            repls = [Repl() for _ in range(per_iter)]
            t_import = time.perf_counter() - t0

            t1 = time.perf_counter()
            repls[0].set_goal("forall n m : Nat, n + m = m + n")
            t_goal = time.perf_counter() - t1

            # Drop the sessions (this triggers the Rust `Drop`, which frees the
            # environment's import regions on the serialized worker) and force a
            # GC before sampling RSS, so a working fix reads as flat RSS.
            del repls
            gc.collect()

            rss = current_rss_mb()
            first = rss if first is None else first
            last = rss
            peak = max(peak, rss)
            print(f"i={i:3d}  import={t_import:7.3f}s  goal={t_goal:7.3f}s  rss={rss:9.1f}MB")
    except Exception as e:  # surface maxHeartbeats / OOM / Lean errors as FAIL
        print(f"FAIL: {type(e).__name__}: {e}")
        return 1

    growth = last - first
    print()
    print(
        f"iterations={iterations}  repl/iter={per_iter}  "
        f"first_rss={first:.1f}MB  last_rss={last:.1f}MB  peak_rss={peak:.1f}MB  "
        f"growth={growth:.1f}MB"
    )
    if growth > max_growth_mb:
        print(
            f"FAIL: RSS grew {growth:.1f} MB over {iterations} iterations "
            f"(limit {max_growth_mb:.0f} MB) — import-region leak (W-407 Bug A) not fixed"
        )
        return 1
    print(f"OK: RSS stable (growth {growth:.1f} MB <= {max_growth_mb:.0f} MB), no maxHeartbeats, no OOM")
    return 0


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print(__doc__)
        raise SystemExit(2)
    raise SystemExit(main(sys.argv[1:]))