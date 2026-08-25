"""Smoke tests for the leotower native bindings."""

import re
from pathlib import Path

import pytest

import leotower


def test_nat_roundtrip():
    with leotower.with_lean() as lean:
        assert lean.nat_roundtrip(0) == 0
        assert lean.nat_roundtrip(42) == 42
        # largest small nat (2^62 - 1); beyond this leo3's to_usize
        # intentionally refuses (big-nat -> usize conversion)
        assert lean.nat_roundtrip(2**62 - 1) == 2**62 - 1
        with pytest.raises(RuntimeError, match="too large"):
            lean.nat_roundtrip(2**63)


def test_nat_add():
    with leotower.with_lean() as lean:
        assert lean.nat_add(20, 22) == 42
        # big-nat path (sum exceeds the small-nat representation)
        assert lean.nat_add(2**60, 2**60) == 2**61


def test_pow_str():
    with leotower.with_lean() as lean:
        assert lean.pow_str(2, 100) == str(2**100)
        assert lean.pow_str(10, 30) == str(10**30)


def test_string_roundtrip():
    with leotower.with_lean() as lean:
        assert lean.string_roundtrip("hello") == "hello"
        assert lean.string_roundtrip("") == ""
        assert lean.string_roundtrip("你好, Lean!") == "你好, Lean!"
        # embedded NUL bytes survive the round trip
        assert lean.string_roundtrip("a\x00b") == "a\x00b"


def test_repeated_sessions():
    """Multiple with_lean() scopes share the one runtime."""
    with leotower.with_lean() as lean:
        assert lean.nat_add(1, 2) == 3
    with leotower.with_lean() as lean:
        assert lean.nat_add(2, 3) == 5


def test_version_matches_pyproject():
    """leotower.__version__ matches the version declared in pyproject.toml
    (importlib.metadata when the distribution metadata is installed,
    hardcoded fallback otherwise)."""
    pyproject = Path(leotower.__file__).resolve().parents[2] / "pyproject.toml"
    declared = re.search(
        r'^version\s*=\s*"([^"]+)"', pyproject.read_text(encoding="utf-8"), re.M
    ).group(1)
    assert leotower.__version__ == declared
