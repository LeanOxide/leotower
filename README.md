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
| `Repl.set_goal(type_str)` | parse + elaborate a term as a new root goal state (existing states unaffected); returns the new state's id (`0` for the first call in a fresh session) |
| `Repl.run_tac(state, tactic, goal_idx=0)` | apply a tactic to the `goal_idx`-th goal; unworked goals are preserved in the new state |
| `Repl.run_tacs(state, tactics, goal_idx=0)` | apply a tactic sequence in order, one call end to end; returns the final state id |
| `Repl.try_run_tac(state, tactic, goal_idx=0)` | non-raising `run_tac`: returns `(state_id, success)` — the new state and `True` on success, the source state and `False` on failure (no state appended); the session stays usable. The core idiom for proof-search / RL loops |
| `Repl.try_run_tacs(state, tactics, goal_idx=0)` | non-raising `run_tacs`: apply a tactic sequence left to right, returning `(state_id, success)` — the final state and `True` if all succeed, the state after the last successful tactic and `False` if one fails |
| `Repl.get_goals(state)` | remaining goals as `Goal(hyps, ty, mvar)`, pretty-printed with Lean's real delaborator |
| `Repl.get_num_goals(state)` | number of remaining goals |
| `Repl.get_goal_pp(state, goal_idx=0)` | pretty-printed goal (hypotheses + `⊢ type`) |
| `Repl.get_state_pp(state)` | pretty-print every goal of `state` in one string: `no goals` with 0 goals, exactly the `get_goal_pp(state, 0)` output for a single goal, numbered `goal[0]:\n<pp0>` blocks joined by a blank line for N goals |
| `Goal.__str__` | standard goal display: one `name : type` line per hypothesis followed by `⊢ ty` (just `⊢ ty` with no hypotheses) — the same `hyps ⊢ type` shape as `get_goal_pp` |
| `Repl.num_states()` | number of replay states created so far; valid ids are `0..num_states()` (half-open — highest valid id is `num_states() - 1`) |
| `Repl.check(term, state=None, goal_idx=0)` | `#check`-style query: `"{term} : {type}"`; `state=None` checks in the root context, `state=N` in that goal's local context. A bare constant prints its declared type (as the real `#check` does, with implicit/universe arguments as binders); other terms are elaborated in the goal context |
| `Repl.inspect(name)` | `#print`-style query: kind, type, and (for definitions/theorems/opaque constants) value, rendered by Lean's real pretty printer |
| `Repl.run_cmd(cmd)` | parse and elaborate a command (e.g. `def`/`theorem`/`axiom`); the resulting environment is installed for subsequent calls. Returns `None` — use `inspect` to view what it defined |
| `Repl.env_has_const(name)` | environment lookup |

Tactic failures raise `RuntimeError` with the elaborator's error message
(`tactic error: ...`); the session stays usable afterwards. For
proof-search / RL loops that must *test* a tactic without exception
handling, use the non-raising `try_run_tac` / `try_run_tacs`, which return
`(state_id, success)` instead of raising.

Known limitations:

- The default `simp` rule set does not make progress on metavariable-applied
  goal types (induction step cases) in the embedded elaborator — use
  `simp only [...]` there. This mirrors upstream: the same rule set behaves
  the same way under the system `lean` binary.

### Mathlib

`Repl("Mathlib")` imports a [lake](https://leanprover.github.io/lean4/doc/lake.html)-built
Mathlib checkout and exposes its tactics (`linarith`, `ring`, `norm_num`,
`omega`, the full `simp` set, ...). Point `LEAN_PATH` at the checkout's build
directories — `lake env printenv LEAN_PATH` in the checkout prints them:

```bash
# one-time: clone the mathlib tag matching the toolchain and build it
git clone --branch v4.25.2 https://github.com/leanprover-community/mathlib4
cd mathlib4 && lake build
```

```python
import os

os.environ["LEAN_PATH"] = (
    "/path/to/mathlib4/.lake/build/lib/lean:"
    "/path/to/mathlib4/.lake/packages/batteries/.lake/build/lib/lean:"
    # ... plus the remaining lake package dirs (aesop, Qq, Cli, ...)
)

from leotower import Repl

repl = Repl("Mathlib")                    # full library, ~7s import
s0 = repl.set_goal("∀ n m : Nat, n + m = m + n")
s1 = repl.run_tac(s0, "intro n m")
s2 = repl.run_tac(s1, "linarith")         # mathlib tactic
assert repl.get_num_goals(s2) == 0
```

The search path is re-read on every `Repl`, so `LEAN_PATH` may be set (or
changed) at any time before a `Repl` is constructed.

Each import re-enables Lean's initializer execution, so core `Lean` and
`Mathlib` Repl sessions may safely coexist in one process.

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

## CI/CD

Workflows live in `.github/workflows/`:

- **`ci.yml`** — on push to `main`, on every PR, and on manual dispatch.
  Builds the extension and runs the pytest suite on
  Ubuntu (Python 3.12 + 3.13), macOS (x86_64 + arm64), and Windows
  (Python 3.12), against the Lean toolchain pinned in `lean-toolchain`.
  Because `leo3` is a local path dependency, the workflow checks out the
  `leo3` repo as a sibling of the `leotower` checkout (tracking `main`;
  override the ref with the `leo3_ref` dispatch input to test against a
  leo3 branch or commit).
  On macOS the test step sets `DYLD_LIBRARY_PATH` to the elan
  toolchain's Lean lib dir: the built extension references Lean's
  dylibs via `@rpath` without an embedded `LC_RPATH`, so dyld needs
  the hint to find them (the runtime mechanism leo3 documents for
  macOS).
  On Windows `import leotower` registers the Lean toolchain's `bin`
  dir (from `LEAN_HOME`, or the elan toolchains under
  `~/.elan/toolchains`) as a DLL search path, since the Windows
  loader does not reliably find Lean's DLLs via `PATH`.
- **`release.yml`** — on version tags (`v*`) or manual dispatch. Builds
  `maturin` wheels for Linux x86_64 and macOS x86_64/arm64, plus the
  sdist, then publishes to PyPI and creates a GitHub Release with the
  artifacts. Manual dispatches only publish when the `publish` input is
  set. A `resolve-leo3` job resolves the leo3 ref to a single full
  commit SHA before any build, and every build job (wheels matrix +
  sdist) checks out that exact SHA, so all artifacts in one release use
  the same leo3 revision.
  No Windows wheel is published yet: constructing `Repl()` aborts the
  process on Windows (leo3 issue, tracked as W-395). Windows is
  covered by the CI smoke tests only (build + import + session tests;
  the Repl test suite is skipped there until W-395 is fixed).

Published builds resolve the `leo3` dependency two ways:

- **git mode (default)** — build against `leo3` at `leo3_ref` (default
  `main`); the `resolve-leo3` job resolves the ref to a full commit
  SHA and every build job checks that SHA out as a sibling. The sdist
  pins leo3 to that commit so it builds standalone.
- **crates.io mode** — set the `leo3_pin` input to a published leo3
  version and both wheels and the sdist pin the crates.io release, per
  the note in `Cargo.toml`. Note: leotower currently uses APIs that only
  exist on leo3 `main` (`leo3::meta::repl`, `MetaMContext` snapshot
  methods), so no published leo3 version compiles yet — use git mode
  until leo3 ships a release with those APIs.

PyPI publishing requires a `PYPI_API_TOKEN` repository secret (an API token
for the PyPI project).
