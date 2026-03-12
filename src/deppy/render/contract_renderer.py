"""Render synthesized contracts as source code.

ContractRenderer formats generated contracts in three styles:
- **Decorator syntax**: ``@requires(...) @ensures(...)``
- **Inline assertions**: ``assert`` statements at function entry/exit.
- **Docstring syntax**: NumPy-style docstring with contract sections.
"""

from __future__ import annotations

import textwrap
from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    List,
    Optional,
    Sequence,
    Tuple,
)

from deppy.core._protocols import TrustLevel


# ---------------------------------------------------------------------------
# Contract data protocol (duck-typed to avoid circular imports)
# ---------------------------------------------------------------------------

class _ContractLike:
    """Protocol for contract-like objects from generate.contract_generator."""

    function_name: str
    requires: Sequence[Any]
    ensures: Sequence[Any]
    raises: Sequence[Any]
    confidence: float


# ---------------------------------------------------------------------------
# Rendering configuration
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class RenderConfig:
    """Configuration for contract rendering.

    Attributes:
        indent: Number of spaces per indentation level.
        max_line_length: Maximum line length before wrapping.
        show_trust: Whether to include trust annotations.
        show_confidence: Whether to show confidence scores.
        style: 'decorator', 'inline', or 'docstring'.
    """

    _indent: int = 4
    _max_line_length: int = 88
    _show_trust: bool = False
    _show_confidence: bool = False
    _style: str = "decorator"

    @property
    def indent(self) -> int:
        return self._indent

    @property
    def max_line_length(self) -> int:
        return self._max_line_length

    @property
    def show_trust(self) -> bool:
        return self._show_trust

    @property
    def show_confidence(self) -> bool:
        return self._show_confidence

    @property
    def style(self) -> str:
        return self._style


# ---------------------------------------------------------------------------
# ContractRenderer
# ---------------------------------------------------------------------------

class ContractRenderer:
    """Render synthesized contracts as source code.

    Supports decorator syntax, inline assertion syntax, and docstring
    syntax for contract annotations.

    Usage::

        renderer = ContractRenderer()
        text = renderer.render(contracts)
        # or for a single contract:
        decorator_text = renderer.render_decorator(contract)
        inline_text = renderer.render_inline(contract)
        docstring_text = renderer.render_docstring(contract)
    """

    def __init__(
        self,
        config: Optional[RenderConfig] = None,
    ) -> None:
        self._config = config or RenderConfig()

    def render(
        self,
        contracts: Sequence[Any],
    ) -> str:
        """Render a list of contracts in the configured style.

        Dispatches to render_decorator, render_inline, or render_docstring
        based on the config style.
        """
        style = self._config.style
        parts: List[str] = []

        for contract in contracts:
            if style == "decorator":
                parts.append(self.render_decorator(contract))
            elif style == "inline":
                parts.append(self.render_inline(contract))
            elif style == "docstring":
                parts.append(self.render_docstring(contract))
            else:
                parts.append(self.render_decorator(contract))

        return "\n\n".join(parts)

    def render_decorator(self, contract: Any) -> str:
        """Render a contract as decorator syntax.

        Produces output like:
            @requires(lambda x: x > 0)
            @ensures(lambda result: result >= 0)
            def func(x: int) -> int: ...
        """
        lines: List[str] = []
        indent = " " * self._config.indent

        func_name = getattr(contract, "function_name", "unknown")
        requires = getattr(contract, "requires", ())
        ensures = getattr(contract, "ensures", ())
        raises = getattr(contract, "raises", ())
        confidence = getattr(contract, "confidence", 1.0)

        for clause in requires:
            expr = getattr(clause, "expression", str(clause))
            trust = getattr(clause, "trust", None)
            line = f"@requires(lambda: {expr})"
            if self._config.show_trust and trust is not None:
                trust_val = trust.value if hasattr(trust, "value") else str(trust)
                line += f"  # trust={trust_val}"
            lines.append(line)

        for clause in ensures:
            expr = getattr(clause, "expression", str(clause))
            trust = getattr(clause, "trust", None)
            line = f"@ensures(lambda result: {expr})"
            if self._config.show_trust and trust is not None:
                trust_val = trust.value if hasattr(trust, "value") else str(trust)
                line += f"  # trust={trust_val}"
            lines.append(line)

        for clause in raises:
            expr = getattr(clause, "expression", str(clause))
            line = f"@raises({expr})"
            lines.append(line)

        if self._config.show_confidence:
            lines.append(f"# confidence: {confidence:.0%}")

        sig_line = f"def {func_name}(...):"
        lines.append(sig_line)
        lines.append(f"{indent}...")

        return "\n".join(lines)

    def render_inline(self, contract: Any) -> str:
        """Render a contract as inline assertion statements.

        Produces output like:
            def func(x: int) -> int:
                assert x > 0, "requires: x > 0"
                result = ...
                assert result >= 0, "ensures: result >= 0"
                return result
        """
        lines: List[str] = []
        indent = " " * self._config.indent

        func_name = getattr(contract, "function_name", "unknown")
        requires = getattr(contract, "requires", ())
        ensures = getattr(contract, "ensures", ())
        raises = getattr(contract, "raises", ())

        lines.append(f"def {func_name}(...):")

        for clause in requires:
            expr = getattr(clause, "expression", str(clause))
            lines.append(
                f'{indent}assert {expr}, "requires: {_escape_str(expr)}"'
            )

        if requires and (ensures or raises):
            lines.append("")

        if ensures:
            lines.append(f"{indent}result = ...  # function body")
            lines.append("")
            for clause in ensures:
                expr = getattr(clause, "expression", str(clause))
                lines.append(
                    f'{indent}assert {expr}, "ensures: {_escape_str(expr)}"'
                )
            lines.append(f"{indent}return result")
        else:
            lines.append(f"{indent}...")

        return "\n".join(lines)

    def render_docstring(self, contract: Any) -> str:
        """Render a contract as a NumPy-style docstring.

        Produces output like:
            def func(x: int) -> int:
                \"\"\"Description.

                Requires
                --------
                x > 0

                Ensures
                -------
                result >= 0
                \"\"\"
        """
        lines: List[str] = []
        indent = " " * self._config.indent

        func_name = getattr(contract, "function_name", "unknown")
        requires = getattr(contract, "requires", ())
        ensures = getattr(contract, "ensures", ())
        raises = getattr(contract, "raises", ())
        confidence = getattr(contract, "confidence", 1.0)

        lines.append(f"def {func_name}(...):")
        lines.append(f'{indent}"""')

        if requires:
            lines.append(f"{indent}Requires")
            lines.append(f"{indent}--------")
            for clause in requires:
                expr = getattr(clause, "expression", str(clause))
                lines.append(f"{indent}{expr}")
            lines.append("")

        if ensures:
            lines.append(f"{indent}Ensures")
            lines.append(f"{indent}-------")
            for clause in ensures:
                expr = getattr(clause, "expression", str(clause))
                lines.append(f"{indent}{expr}")
            lines.append("")

        if raises:
            lines.append(f"{indent}Raises")
            lines.append(f"{indent}------")
            for clause in raises:
                expr = getattr(clause, "expression", str(clause))
                lines.append(f"{indent}{expr}")
            lines.append("")

        if self._config.show_confidence:
            lines.append(f"{indent}Confidence: {confidence:.0%}")
            lines.append("")

        lines.append(f'{indent}"""')
        lines.append(f"{indent}...")

        return "\n".join(lines)

    def render_diff(
        self,
        old_contract: Optional[Any],
        new_contract: Any,
    ) -> str:
        """Render a diff between an old and new contract."""
        lines: List[str] = []

        new_requires = set(
            getattr(c, "expression", str(c))
            for c in getattr(new_contract, "requires", ())
        )
        new_ensures = set(
            getattr(c, "expression", str(c))
            for c in getattr(new_contract, "ensures", ())
        )

        old_requires: set[str] = set()
        old_ensures: set[str] = set()
        if old_contract is not None:
            old_requires = set(
                getattr(c, "expression", str(c))
                for c in getattr(old_contract, "requires", ())
            )
            old_ensures = set(
                getattr(c, "expression", str(c))
                for c in getattr(old_contract, "ensures", ())
            )

        added_req = new_requires - old_requires
        removed_req = old_requires - new_requires
        added_ens = new_ensures - old_ensures
        removed_ens = old_ensures - new_ensures

        func_name = getattr(new_contract, "function_name", "unknown")
        lines.append(f"Contract diff for {func_name}:")

        for expr in sorted(added_req):
            lines.append(f"  + @requires {expr}")
        for expr in sorted(removed_req):
            lines.append(f"  - @requires {expr}")
        for expr in sorted(added_ens):
            lines.append(f"  + @ensures {expr}")
        for expr in sorted(removed_ens):
            lines.append(f"  - @ensures {expr}")

        if not (added_req or removed_req or added_ens or removed_ens):
            lines.append("  (no changes)")

        return "\n".join(lines)


def _escape_str(s: str) -> str:
    """Escape a string for use inside an assertion message."""
    return s.replace('"', '\\"').replace("'", "\\'")
