"""Tests for the Python effect model."""
from __future__ import annotations

import pytest
from cctt.proof_theory.effect_model import (
    EffectType, FunctionEffect, StateContract, EffectAnalyzer,
    synthesize_state_contract, analyze_effects, _max_effect,
)


class TestEffectType:
    def test_pure_is_pure(self):
        assert EffectType.PURE.is_pure
        assert not EffectType.MUTATES_SELF.is_pure

    def test_equational_reasoning(self):
        assert EffectType.PURE.allows_equational
        assert EffectType.READS_STATE.allows_equational
        assert not EffectType.MUTATES_SELF.allows_equational
        assert not EffectType.IO.allows_equational
        assert not EffectType.NONDETERMINISTIC.allows_equational

    def test_severity_ordering(self):
        assert EffectType.PURE.severity < EffectType.READS_STATE.severity
        assert EffectType.READS_STATE.severity < EffectType.MUTATES_SELF.severity
        assert EffectType.MUTATES_SELF.severity < EffectType.MUTATES_ARGS.severity
        assert EffectType.MUTATES_ARGS.severity < EffectType.MUTATES_GLOBAL.severity
        assert EffectType.MUTATES_GLOBAL.severity < EffectType.IO.severity
        assert EffectType.IO.severity < EffectType.NONDETERMINISTIC.severity

    def test_max_effect(self):
        assert _max_effect(EffectType.PURE, EffectType.IO) == EffectType.IO
        assert _max_effect() == EffectType.PURE
        assert _max_effect(EffectType.MUTATES_SELF) == EffectType.MUTATES_SELF


class TestFunctionEffect:
    def test_pure_effect(self):
        e = FunctionEffect()
        assert e.is_pure
        assert e.modifies == frozenset()

    def test_combine(self):
        e1 = FunctionEffect(
            effect_type=EffectType.MUTATES_SELF,
            writes=frozenset({"self.x"}),
        )
        e2 = FunctionEffect(
            effect_type=EffectType.IO,
            io_operations=frozenset({"open"}),
        )
        combined = e1.combine(e2)
        assert combined.effect_type == EffectType.IO
        assert "self.x" in combined.writes
        assert "open" in combined.io_operations

    def test_serialization_roundtrip(self):
        e = FunctionEffect(
            effect_type=EffectType.MUTATES_ARGS,
            reads=frozenset({"self.items"}),
            writes=frozenset({"self.count"}),
            calls_mutating=frozenset({"list.append"}),
            raises=frozenset({"ValueError"}),
        )
        j = e.to_json()
        e2 = FunctionEffect.from_json(j)
        assert e2.effect_type == EffectType.MUTATES_ARGS
        assert "self.items" in e2.reads
        assert "self.count" in e2.writes
        assert "list.append" in e2.calls_mutating
        assert "ValueError" in e2.raises


class TestStateContract:
    def test_trivial(self):
        sc = StateContract()
        assert sc.is_trivial

    def test_non_trivial(self):
        sc = StateContract(
            modifies=frozenset({"self.items"}),
            old_bindings={"old_len": "len(self.items)"},
            post_ensures=["len(self.items) == old_len + 1"],
        )
        assert not sc.is_trivial
        assert "self.items" in sc.modifies
        assert sc.old_bindings["old_len"] == "len(self.items)"

    def test_serialization(self):
        sc = StateContract(
            modifies=frozenset({"self"}),
            pre_requires=["len(self) > 0"],
            post_ensures=["len(self) == old_len - 1"],
            exceptional_post={"IndexError": ["isinstance(raised, IndexError)"]},
        )
        j = sc.to_json()
        sc2 = StateContract.from_json(j)
        assert "self" in sc2.modifies
        assert sc2.pre_requires == ["len(self) > 0"]
        assert "IndexError" in sc2.exceptional_post


class TestEffectAnalyzer:
    """Test effect detection from Python source code."""

    def test_pure_function(self):
        src = "def add(a, b):\n    return a + b"
        e = analyze_effects(src, "add")
        assert e.is_pure
        assert e.effect_type == EffectType.PURE

    def test_pure_with_local_mutation(self):
        src = "def f(x):\n    result = []\n    result.append(x)\n    return result"
        e = analyze_effects(src, "f")
        # Local variable mutation — not a param, so classified as pure
        assert e.effect_type == EffectType.PURE

    def test_self_attr_write(self):
        src = "def set_value(self, v):\n    self.value = v"
        e = analyze_effects(src, "set_value")
        assert e.effect_type == EffectType.MUTATES_SELF
        assert "self.value" in e.writes

    def test_self_attr_write_in_init(self):
        src = "def __init__(self, x):\n    self.x = x"
        e = analyze_effects(src, "__init__")
        # __init__ is allowed to set self attributes — NOT classified as mutation
        assert e.effect_type == EffectType.PURE

    def test_self_method_mutation(self):
        src = "def push(self, x):\n    self.items.append(x)"
        e = analyze_effects(src, "push")
        assert e.effect_type == EffectType.MUTATES_SELF
        assert "self.items.append" in e.calls_mutating

    def test_arg_mutation(self):
        src = "def add_item(lst, item):\n    lst.append(item)"
        e = analyze_effects(src, "add_item")
        assert e.effect_type == EffectType.MUTATES_ARGS
        assert "lst.append" in e.calls_mutating

    def test_global_mutation(self):
        src = "_cache = {}\ndef clear_cache():\n    global _cache\n    _cache = {}"
        e = analyze_effects(src, "clear_cache")
        assert e.effect_type == EffectType.MUTATES_GLOBAL

    def test_global_subscript_mutation(self):
        src = "_cache = {}\ndef set_cache(k, v):\n    global _cache\n    _cache[k] = v"
        e = analyze_effects(src, "set_cache")
        assert e.effect_type == EffectType.MUTATES_GLOBAL
        assert "_cache" in e.globals_written

    def test_io_open(self):
        src = 'def save(path, data):\n    f = open(path, "w")\n    f.write(data)'
        e = analyze_effects(src, "save")
        assert e.effect_type == EffectType.IO
        assert "open" in e.io_operations

    def test_io_print(self):
        src = "def show(x):\n    print(x)"
        e = analyze_effects(src, "show")
        assert e.effect_type == EffectType.IO

    def test_nondeterministic_random(self):
        src = "import random\ndef flip():\n    return random.randint(0, 1)"
        e = analyze_effects(src, "flip")
        assert e.effect_type == EffectType.NONDETERMINISTIC

    def test_exception_raise(self):
        src = "def div(a, b):\n    if b == 0:\n        raise ZeroDivisionError('bad')\n    return a / b"
        e = analyze_effects(src, "div")
        assert "ZeroDivisionError" in e.raises

    def test_exception_catch(self):
        src = "def safe_div(a, b):\n    try:\n        return a / b\n    except ZeroDivisionError:\n        return 0"
        e = analyze_effects(src, "safe_div")
        assert "ZeroDivisionError" in e.catches

    def test_setattr_builtin(self):
        src = "def set_val(self, name, val):\n    setattr(self, name, val)"
        e = analyze_effects(src, "set_val")
        assert e.effect_type == EffectType.MUTATES_SELF

    def test_dict_update(self):
        src = "def merge(d, other):\n    d.update(other)"
        e = analyze_effects(src, "merge")
        assert e.effect_type == EffectType.MUTATES_ARGS
        assert "d.update" in e.calls_mutating

    def test_list_sort_in_place(self):
        src = "def sort_list(data):\n    data.sort()"
        e = analyze_effects(src, "sort_list")
        assert e.effect_type == EffectType.MUTATES_ARGS
        assert "data.sort" in e.calls_mutating

    def test_self_subscript_write(self):
        src = "def __setitem__(self, key, value):\n    self[key] = value"
        e = analyze_effects(src, "__setitem__")
        assert e.effect_type == EffectType.MUTATES_SELF
        assert "self[*]" in e.writes

    def test_reads_self_attributes(self):
        src = "def get_name(self):\n    return self.name"
        e = analyze_effects(src, "get_name")
        assert "self.name" in e.reads
        assert e.effect_type == EffectType.READS_STATE

    def test_syntax_error_conservative(self):
        src = "def bad(:\n    pass"
        e = analyze_effects(src, "bad")
        assert not e.is_pure  # Conservative: can't parse → impure

    def test_missing_function_conservative(self):
        src = "def other(): pass"
        e = analyze_effects(src, "nonexistent")
        assert not e.is_pure


class TestSynthesizeStateContract:
    def test_pure_trivial(self):
        e = FunctionEffect()
        sc = synthesize_state_contract(e)
        assert sc.is_trivial

    def test_append_contract(self):
        e = FunctionEffect(
            effect_type=EffectType.MUTATES_SELF,
            calls_mutating=frozenset({"self.items.append"}),
        )
        sc = synthesize_state_contract(e, "push", ["self", "x"])
        assert not sc.is_trivial
        assert any("len(" in p for p in sc.post_ensures)

    def test_pop_contract(self):
        e = FunctionEffect(
            effect_type=EffectType.MUTATES_SELF,
            calls_mutating=frozenset({"self.pop"}),
        )
        sc = synthesize_state_contract(e, "remove_last", ["self"])
        assert any("len(" in p for p in sc.post_ensures)
        assert any("len(" in p for p in sc.pre_requires)

    def test_clear_contract(self):
        e = FunctionEffect(
            effect_type=EffectType.MUTATES_SELF,
            calls_mutating=frozenset({"self.clear"}),
        )
        sc = synthesize_state_contract(e, "reset", ["self"])
        assert any("len(self) == 0" in p for p in sc.post_ensures)

    def test_sort_contract(self):
        e = FunctionEffect(
            effect_type=EffectType.MUTATES_ARGS,
            calls_mutating=frozenset({"data.sort"}),
        )
        sc = synthesize_state_contract(e, "sort_data", ["data"])
        # Sort preserves length
        assert any("len(data)" in p for p in sc.post_ensures)

    def test_exception_contract(self):
        e = FunctionEffect(
            effect_type=EffectType.READS_STATE,
            raises=frozenset({"ValueError", "TypeError"}),
        )
        sc = synthesize_state_contract(e, "validate")
        assert "ValueError" in sc.exceptional_post
        assert "TypeError" in sc.exceptional_post


class TestC4SpecEffectIntegration:
    """Test that C4Spec correctly includes effects."""

    def test_pure_spec_no_effects(self):
        from cctt.proof_theory.spec_inference import infer_c4_spec
        spec = infer_c4_spec("def add(a, b):\n    return a + b", "add", ["a", "b"])
        assert spec.purity is True
        assert spec.effects is None
        assert spec.state_contract is None

    def test_mutating_spec_has_effects(self):
        from cctt.proof_theory.spec_inference import infer_c4_spec
        spec = infer_c4_spec(
            "def push(self, x):\n    self.items.append(x)",
            "push", ["self", "x"],
        )
        assert spec.purity is False
        assert spec.effects is not None
        assert spec.effects.effect_type == EffectType.MUTATES_SELF
        assert spec.state_contract is not None
        assert not spec.state_contract.is_trivial

    def test_io_spec_has_effects(self):
        from cctt.proof_theory.spec_inference import infer_c4_spec
        spec = infer_c4_spec(
            'def save(path):\n    f = open(path, "w")\n    f.write("data")',
            "save", ["path"],
        )
        assert spec.purity is False
        assert spec.effects is not None
        assert spec.effects.effect_type == EffectType.IO

    def test_effect_serialization_roundtrip(self):
        from cctt.proof_theory.spec_inference import infer_c4_spec, C4Spec
        spec = infer_c4_spec(
            "def push(self, x):\n    self.items.append(x)",
            "push", ["self", "x"],
        )
        j = spec.to_json()
        assert "effects" in j
        assert "state_contract" in j
        spec2 = C4Spec.from_json(j)
        assert spec2.effects is not None
        assert spec2.effects.effect_type == EffectType.MUTATES_SELF
        assert spec2.state_contract is not None

    def test_mutating_ensures_include_state_postconditions(self):
        from cctt.proof_theory.spec_inference import infer_c4_spec
        spec = infer_c4_spec(
            "def push(self, x):\n    self.items.append(x)",
            "push", ["self", "x"],
        )
        # State contract postconditions should be merged into ensures
        assert any("len(" in e for e in spec.ensures)

    def test_arg_mutation_ensures(self):
        from cctt.proof_theory.spec_inference import infer_c4_spec
        spec = infer_c4_spec(
            "def add_item(lst, item):\n    lst.append(item)",
            "add_item", ["lst", "item"],
        )
        assert spec.purity is False
        assert any("len(lst)" in e for e in spec.ensures)
