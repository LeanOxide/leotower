# leotower

Python bindings for [Leo3](https://github.com/AndPuQing/leo3) — safe,
ergonomic Rust bindings for the [Lean4](https://github.com/leanprover/lean4)
theorem prover. Built with [PyO3](https://pyo3.rs) and
[maturin](https://www.maturin.rs).

The native extension embeds Lean's real runtime in-process: no subprocess per
call, no ctypes over the C API. Python threads attach to the shared Lean
runtime on first use and run conversions and computations on real Lean
objects.

## Quick start

Requires a Lean 4.25.2 toolchain on `PATH` (install via
[elan](https://github.com/leanprover/elan)).

```python
import leotower

with leotower.with_lean() as lean:
    assert lean.nat_add(20, 22) == 42
    assert lean.pow_str(2, 100) == "1267650600228229401496703205376"
    assert lean.string_roundtrip("你好, Lean!") == "你好, Lean!"
```

## API

| Python | Lean runtime |
|---|---|
| `leotower.with_lean()` | context manager ensuring one-time runtime bootstrap + thread attach |
| `LeanSession.nat_roundtrip(n)` | `usize` ↔ `Nat` round trip |
| `LeanSession.nat_add(a, b)` | `Nat.add` (small + big nat paths) |
| `LeanSession.pow_str(a, b)` | `Nat.pow`, decimal string (exact beyond `u64`) |
| `LeanSession.string_roundtrip(s)` | `String` round trip (NUL-safe) |

## Why embed instead of subprocess?

Every Lean interaction today costs either a full process start or a
protocol round trip. The benchmark in `bench/benchmark.py` measures a hot
in-process call against one cold `lean --run` per request:

```
embedded : 20000 calls in 0.044s  -> 2.2 us/call
subprocess: 20 calls in 8.498s  -> 424.88 ms/call
speedup  : 193657x
```

That gap is the steady-state cost of one step in a proof-search or RL loop —
the workload that AI-for-math tooling (LeanDojo-style pipelines) pays per
step today.

## Development

```bash
uv sync                       # create venv with maturin + pytest
uv run maturin develop        # build the extension in place
uv run pytest                 # run the test suite
uv run python bench/benchmark.py
```

`Cargo.toml` pins `leo3` to the local `../leo3/leo3` crate for development;
switch to the crates.io release for published builds.
