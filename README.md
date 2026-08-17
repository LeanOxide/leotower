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

## Repl — LeanDojo-compatible replay layer

`leotower.Repl` is a LeanDojo v2-style replay session over the embedded
runtime: import a module, set a goal, apply tactics step by step, and query
the remaining goals. Everything runs on Lean's real elaborator in-process.

```python
from leotower import Repl

repl = Repl()                      # imports Lean
s0 = repl.set_goal("∀ n m : Nat, n + m = m + n")
assert repl.get_num_goals(s0) == 1

s1 = repl.run_tac(s0, "intro n m")
assert repl.get_num_goals(s1) == 1
assert "n m : Nat" in repl.get_goal_pp(s1)

s2 = repl.run_tac(s1, "induction n")     # base + step goals
assert repl.get_num_goals(s2) == 2

# Unworked goals are preserved, so multi-goal states advance in any order:
s3 = repl.run_tac(s2, "simp only [Nat.add_comm, Nat.add_succ]", goal_idx=1)
assert repl.get_num_goals(s3) == 1
s4 = repl.run_tac(s3, "simp only [Nat.zero_add, Nat.add_zero]", goal_idx=0)
assert repl.get_num_goals(s4) == 0
```

| Method | Behavior |
|---|---|
| `Repl(module="Lean")` | import a module (dot-separated names, or a `.lean` file path whose top-level commands are elaborated) into a fresh environment |
| `Repl.set_goal(type_str)` | parse + elaborate a term as the root goal type; returns state 0 |
| `Repl.run_tac(state, tactic, goal_idx=0)` | apply a tactic to the `goal_idx`-th goal; unworked goals are preserved in the new state |
| `Repl.get_goals(state)` | remaining goals as `Goal(hyps, ty, mvar)`, pretty-printed with Lean's real delaborator |
| `Repl.get_num_goals(state)` | number of remaining goals |
| `Repl.get_goal_pp(state, goal_idx=0)` | pretty-printed goal (hypotheses + `⊢ type`) |
| `Repl.run_cmd(cmd)` | parse and elaborate a command (e.g. `def`/`theorem`); the resulting environment is installed for subsequent calls |
| `Repl.env_has_const(name)` | environment lookup |

Tactic failures raise `RuntimeError` with the elaborator's error message
(`tactic error: ...`); the session stays usable afterwards.

Known limitation: the default `simp` rule set does not make progress on
metavariable-applied goal types (induction step cases) in the embedded
elaborator — use `simp only [...]` there. This mirrors upstream: the same
rule set behaves the same way under the system `lean` binary.

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
