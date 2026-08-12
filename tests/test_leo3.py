"""Smoke tests for the leo3-py native bindings."""

import pytest

import leo3_py


def test_nat_roundtrip():
    with leo3_py.with_lean() as lean:
        assert lean.nat_roundtrip(0) == 0
        assert lean.nat_roundtrip(42) == 42
        # largest small nat (2^62 - 1); beyond this leo3's to_usize
        # intentionally refuses (big-nat -> usize conversion)
        assert lean.nat_roundtrip(2**62 - 1) == 2**62 - 1
        with pytest.raises(RuntimeError, match="too large"):
            lean.nat_roundtrip(2**63)


def test_nat_add():
    with leo3_py.with_lean() as lean:
        assert lean.nat_add(20, 22) == 42
        # big-nat path (sum exceeds the small-nat representation)
        assert lean.nat_add(2**60, 2**60) == 2**61


def test_pow_str():
    with leo3_py.with_lean() as lean:
        assert lean.pow_str(2, 100) == str(2**100)
        assert lean.pow_str(10, 30) == str(10**30)


def test_string_roundtrip():
    with leo3_py.with_lean() as lean:
        assert lean.string_roundtrip("hello") == "hello"
        assert lean.string_roundtrip("") == ""
        assert lean.string_roundtrip("你好, Lean!") == "你好, Lean!"
        # embedded NUL bytes survive the round trip
        assert lean.string_roundtrip("a\x00b") == "a\x00b"


def test_repeated_sessions():
    """Multiple with_lean() scopes share the one runtime."""
    with leo3_py.with_lean() as lean:
        assert lean.nat_add(1, 2) == 3
    with leo3_py.with_lean() as lean:
        assert lean.nat_add(2, 3) == 5
