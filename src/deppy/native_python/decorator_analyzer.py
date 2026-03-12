"""Decorator chain analysis for Python functions and classes.

Analyzes decorator effects on function signatures and types.  In the
sheaf-descent framework, decorators are morphisms that transform the
cover of the decorated function -- they may modify the input/output
boundary, add error sites, or change the type of the callable.

Common decorators with known effects:
- @property: Transforms method to property access (FieldInfo)
- @classmethod: Changes first param from instance to class
- @staticmethod: Removes instance parameter
- @functools.wraps: Preserves wrapper transparency
- @abstractmethod: Marks method as abstract (no implementation)
- @contextmanager: Transforms generator to context manager
- @dataclass: Transforms class definition
"""

from __future__ import annotations

import ast
from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    FrozenSet,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
)


# ---------------------------------------------------------------------------
# Decorator effect
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class DecoratorEffect:
    """Description of a single decorator's effect on a function.

    Attributes:
        _decorator_name: Name of the decorator.
        _effect_kind: Kind of effect (e.g., "signature_change", "type_transform").
        _removes_self: Whether the decorator removes the self/cls parameter.
        _adds_self_type: Whether the decorator adds a type parameter.
        _changes_return_type: Whether the return type is modified.
        _new_return_type_desc: Description of the new return type.
        _preserves_signature: Whether the original signature is preserved.
        _is_wrapper_decorator: Whether this creates a wrapper pattern.
        _is_known: Whether this is a recognized decorator with known semantics.
        _arguments: Arguments passed to the decorator (if it's called).
        _line: Source line number.
    """

    _decorator_name: str
    _effect_kind: str = "unknown"
    _removes_self: bool = False
    _adds_self_type: bool = False
    _changes_return_type: bool = False
    _new_return_type_desc: Optional[str] = None
    _preserves_signature: bool = True
    _is_wrapper_decorator: bool = False
    _is_known: bool = False
    _arguments: Tuple[str, ...] = ()
    _line: int = 0

    @property
    def decorator_name(self) -> str:
        return self._decorator_name

    @property
    def effect_kind(self) -> str:
        return self._effect_kind

    @property
    def removes_self(self) -> bool:
        return self._removes_self

    @property
    def changes_return_type(self) -> bool:
        return self._changes_return_type

    @property
    def new_return_type_desc(self) -> Optional[str]:
        return self._new_return_type_desc

    @property
    def preserves_signature(self) -> bool:
        return self._preserves_signature

    @property
    def is_wrapper_decorator(self) -> bool:
        return self._is_wrapper_decorator

    @property
    def is_known(self) -> bool:
        return self._is_known

    @property
    def arguments(self) -> Tuple[str, ...]:
        return self._arguments


# ---------------------------------------------------------------------------
# Decorator stack result
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class DecoratorStackResult:
    """Analysis result for an entire decorator stack.

    Attributes:
        _func_name: Name of the decorated function.
        _effects: List of effects, outermost first.
        _final_is_property: Whether the result is a property.
        _final_is_classmethod: Whether the result is a classmethod.
        _final_is_staticmethod: Whether the result is a staticmethod.
        _final_is_abstract: Whether the result is abstract.
        _final_is_coroutine: Whether the result is a coroutine.
        _signature_changed: Whether the signature is modified.
        _return_type_changed: Whether the return type is modified.
        _is_transparent: Whether all decorators preserve wrapper transparency.
    """

    _func_name: str
    _effects: Tuple[DecoratorEffect, ...] = ()
    _final_is_property: bool = False
    _final_is_classmethod: bool = False
    _final_is_staticmethod: bool = False
    _final_is_abstract: bool = False
    _final_is_coroutine: bool = False
    _signature_changed: bool = False
    _return_type_changed: bool = False
    _is_transparent: bool = True

    @property
    def func_name(self) -> str:
        return self._func_name

    @property
    def effects(self) -> Tuple[DecoratorEffect, ...]:
        return self._effects

    @property
    def is_property(self) -> bool:
        return self._final_is_property

    @property
    def is_classmethod(self) -> bool:
        return self._final_is_classmethod

    @property
    def is_staticmethod(self) -> bool:
        return self._final_is_staticmethod

    @property
    def is_abstract(self) -> bool:
        return self._final_is_abstract

    @property
    def is_transparent(self) -> bool:
        return self._is_transparent

    @property
    def decorator_count(self) -> int:
        return len(self._effects)


# ---------------------------------------------------------------------------
# Known decorator registry
# ---------------------------------------------------------------------------

def _decorator_name(node: ast.expr) -> str:
    """Extract decorator name from AST node."""
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        return ast.unparse(node)
    if isinstance(node, ast.Call):
        return _decorator_name(node.func)
    return ast.unparse(node)


def _decorator_args(node: ast.expr) -> Tuple[str, ...]:
    """Extract decorator arguments if it's a call."""
    if isinstance(node, ast.Call):
        return tuple(ast.unparse(a) for a in node.args)
    return ()


# Map from decorator name to effect factory
def _analyze_known_decorator(
    name: str,
    args: Tuple[str, ...],
    line: int,
) -> Optional[DecoratorEffect]:
    """Analyze a known decorator and return its effect."""

    # @property
    if name == "property":
        return DecoratorEffect(
            _decorator_name="property",
            _effect_kind="property_transform",
            _changes_return_type=True,
            _new_return_type_desc="property descriptor",
            _preserves_signature=False,
            _is_known=True,
            _line=line,
        )

    # @staticmethod
    if name == "staticmethod":
        return DecoratorEffect(
            _decorator_name="staticmethod",
            _effect_kind="static_method",
            _removes_self=True,
            _preserves_signature=True,
            _is_known=True,
            _line=line,
        )

    # @classmethod
    if name == "classmethod":
        return DecoratorEffect(
            _decorator_name="classmethod",
            _effect_kind="class_method",
            _adds_self_type=True,
            _preserves_signature=True,
            _is_known=True,
            _line=line,
        )

    # @abstractmethod / @abc.abstractmethod
    if name in ("abstractmethod", "abc.abstractmethod"):
        return DecoratorEffect(
            _decorator_name=name,
            _effect_kind="abstract_marker",
            _preserves_signature=True,
            _is_known=True,
            _line=line,
        )

    # @functools.wraps
    if name in ("wraps", "functools.wraps"):
        return DecoratorEffect(
            _decorator_name=name,
            _effect_kind="wrapper_preserve",
            _preserves_signature=True,
            _is_wrapper_decorator=True,
            _is_known=True,
            _arguments=args,
            _line=line,
        )

    # @functools.lru_cache / @functools.cache
    if name in (
        "lru_cache", "functools.lru_cache",
        "cache", "functools.cache",
    ):
        return DecoratorEffect(
            _decorator_name=name,
            _effect_kind="caching",
            _preserves_signature=True,
            _is_known=True,
            _arguments=args,
            _line=line,
        )

    # @contextlib.contextmanager
    if name in ("contextmanager", "contextlib.contextmanager"):
        return DecoratorEffect(
            _decorator_name=name,
            _effect_kind="context_manager_transform",
            _changes_return_type=True,
            _new_return_type_desc="ContextManager",
            _preserves_signature=True,
            _is_known=True,
            _line=line,
        )

    # @contextlib.asynccontextmanager
    if name in ("asynccontextmanager", "contextlib.asynccontextmanager"):
        return DecoratorEffect(
            _decorator_name=name,
            _effect_kind="async_context_manager_transform",
            _changes_return_type=True,
            _new_return_type_desc="AsyncContextManager",
            _preserves_signature=True,
            _is_known=True,
            _line=line,
        )

    # @dataclasses.dataclass / @dataclass
    if name in ("dataclass", "dataclasses.dataclass"):
        return DecoratorEffect(
            _decorator_name=name,
            _effect_kind="dataclass_transform",
            _changes_return_type=False,
            _preserves_signature=False,
            _is_known=True,
            _arguments=args,
            _line=line,
        )

    # @typing.overload
    if name in ("overload", "typing.overload"):
        return DecoratorEffect(
            _decorator_name=name,
            _effect_kind="overload_declaration",
            _preserves_signature=True,
            _is_known=True,
            _line=line,
        )

    # @typing.final
    if name in ("final", "typing.final"):
        return DecoratorEffect(
            _decorator_name=name,
            _effect_kind="final_marker",
            _preserves_signature=True,
            _is_known=True,
            _line=line,
        )

    # @typing.runtime_checkable
    if name in ("runtime_checkable", "typing.runtime_checkable"):
        return DecoratorEffect(
            _decorator_name=name,
            _effect_kind="runtime_checkable_marker",
            _preserves_signature=True,
            _is_known=True,
            _line=line,
        )

    # @pytest.fixture / @pytest.mark.*
    if name.startswith("pytest.") or name in ("fixture",):
        return DecoratorEffect(
            _decorator_name=name,
            _effect_kind="test_framework",
            _preserves_signature=True,
            _is_known=True,
            _arguments=args,
            _line=line,
        )

    return None


# ---------------------------------------------------------------------------
# DecoratorAnalyzer
# ---------------------------------------------------------------------------

class DecoratorAnalyzer:
    """Analyze decorator chains on functions and classes.

    Determines how decorators affect function signatures, return types,
    and wrapper transparency in the sheaf-descent framework.
    """

    def __init__(self) -> None:
        self._analysis_cache: Dict[str, DecoratorStackResult] = {}

    # -- Core analysis ------------------------------------------------------

    def analyze_decorators(
        self,
        func_ast: ast.FunctionDef,
    ) -> List[DecoratorEffect]:
        """Analyze all decorators on a function definition.

        Returns a list of DecoratorEffect instances, outermost first
        (matching the order they appear in source).
        """
        effects: List[DecoratorEffect] = []

        for dec_node in func_ast.decorator_list:
            name = _decorator_name(dec_node)
            args = _decorator_args(dec_node)
            line = getattr(dec_node, "lineno", 0)

            known = _analyze_known_decorator(name, args, line)
            if known is not None:
                effects.append(known)
            else:
                # Unknown decorator
                effects.append(DecoratorEffect(
                    _decorator_name=name,
                    _effect_kind="unknown",
                    _preserves_signature=False,
                    _is_known=False,
                    _arguments=args,
                    _line=line,
                ))

        return effects

    def analyze_stack(
        self,
        func_ast: ast.FunctionDef,
    ) -> DecoratorStackResult:
        """Analyze the complete decorator stack of a function.

        Returns a DecoratorStackResult summarizing the combined effects.
        """
        func_name = func_ast.name
        if func_name in self._analysis_cache:
            return self._analysis_cache[func_name]

        effects = self.analyze_decorators(func_ast)

        is_property = False
        is_classmethod = False
        is_staticmethod = False
        is_abstract = False
        sig_changed = False
        ret_changed = False
        is_transparent = True

        for effect in effects:
            if effect.effect_kind == "property_transform":
                is_property = True
                sig_changed = True
            elif effect.effect_kind == "class_method":
                is_classmethod = True
            elif effect.effect_kind == "static_method":
                is_staticmethod = True
            elif effect.effect_kind == "abstract_marker":
                is_abstract = True

            if effect.changes_return_type:
                ret_changed = True
            if not effect.preserves_signature:
                sig_changed = True
            if not effect.is_known and not effect.is_wrapper_decorator:
                is_transparent = False

        is_async = isinstance(func_ast, ast.AsyncFunctionDef)

        result = DecoratorStackResult(
            _func_name=func_name,
            _effects=tuple(effects),
            _final_is_property=is_property,
            _final_is_classmethod=is_classmethod,
            _final_is_staticmethod=is_staticmethod,
            _final_is_abstract=is_abstract,
            _final_is_coroutine=is_async,
            _signature_changed=sig_changed,
            _return_type_changed=ret_changed,
            _is_transparent=is_transparent,
        )
        self._analysis_cache[func_name] = result
        return result

    # -- Convenience queries ------------------------------------------------

    def is_property(self, func_ast: ast.FunctionDef) -> bool:
        """Check if a function is decorated as a property."""
        for dec in func_ast.decorator_list:
            name = _decorator_name(dec)
            if name == "property":
                return True
            # Also check for @X.setter, @X.deleter patterns
            if isinstance(dec, ast.Attribute) and dec.attr in ("setter", "deleter"):
                return True
        return False

    def is_classmethod(self, func_ast: ast.FunctionDef) -> bool:
        """Check if a function is decorated as a classmethod."""
        for dec in func_ast.decorator_list:
            if _decorator_name(dec) == "classmethod":
                return True
        return False

    def is_staticmethod(self, func_ast: ast.FunctionDef) -> bool:
        """Check if a function is decorated as a staticmethod."""
        for dec in func_ast.decorator_list:
            if _decorator_name(dec) == "staticmethod":
                return True
        return False

    def is_abstract(self, func_ast: ast.FunctionDef) -> bool:
        """Check if a function is decorated as abstract."""
        for dec in func_ast.decorator_list:
            name = _decorator_name(dec)
            if name in ("abstractmethod", "abc.abstractmethod",
                        "abstractproperty", "abc.abstractproperty"):
                return True
        return False

    def has_wraps(self, func_ast: ast.FunctionDef) -> bool:
        """Check if a function uses @functools.wraps."""
        for dec in func_ast.decorator_list:
            name = _decorator_name(dec)
            if name in ("wraps", "functools.wraps"):
                return True
        return False

    def get_decorator_names(
        self, func_ast: ast.FunctionDef
    ) -> List[str]:
        """Return the names of all decorators on a function."""
        return [_decorator_name(d) for d in func_ast.decorator_list]

    # -- Batch analysis -----------------------------------------------------

    def analyze_all_in_class(
        self,
        class_ast: ast.ClassDef,
    ) -> Dict[str, DecoratorStackResult]:
        """Analyze decorators on all methods in a class."""
        results: Dict[str, DecoratorStackResult] = {}
        for item in class_ast.body:
            if isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef)):
                results[item.name] = self.analyze_stack(item)
        return results

    def clear_cache(self) -> None:
        """Clear the analysis cache."""
        self._analysis_cache.clear()
