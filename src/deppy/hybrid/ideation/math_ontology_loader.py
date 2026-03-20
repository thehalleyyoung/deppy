"""Load and query the large math ontology corpus for ideation."""

from __future__ import annotations

import json
from functools import lru_cache
from pathlib import Path
from typing import Any, Dict, Iterable, Optional, Tuple


def ontology_path() -> Path:
    return Path(__file__).with_name("math_ontology_50k.json")


@lru_cache(maxsize=1)
def load_math_ontology() -> Dict[str, Any]:
    with ontology_path().open("r", encoding="utf-8") as handle:
        return json.load(handle)


@lru_cache(maxsize=1)
def ontology_summary() -> Dict[str, Any]:
    payload = load_math_ontology()
    return {
        "root": payload.get("root", "mathematics"),
        "category_count": int(payload.get("category_count", 0)),
        "area_count": int(payload.get("area_count", 0)),
        "term_count": int(payload.get("term_count", 0)),
        "path": str(ontology_path()),
    }


@lru_cache(maxsize=1)
def all_math_areas() -> Tuple[Dict[str, Any], ...]:
    payload = load_math_ontology()
    areas = []
    for category in payload.get("categories", []):
        for area in category.get("areas", []):
            areas.append(area)
    return tuple(areas)


@lru_cache(maxsize=1)
def all_math_terms() -> Tuple[str, ...]:
    payload = load_math_ontology()
    return tuple(payload.get("term_index", {}).keys())


@lru_cache(maxsize=1)
def _area_name_index() -> Dict[str, Dict[str, Any]]:
    return {
        str(area.get("name", "")).strip().lower(): area
        for area in all_math_areas()
        if str(area.get("name", "")).strip()
    }


def lookup_math_area(name: str) -> Optional[Dict[str, Any]]:
    return _area_name_index().get(str(name).strip().lower())


def resolve_math_areas(names: Iterable[str]) -> Tuple[Dict[str, Any], ...]:
    resolved = []
    seen = set()
    for name in names:
        key = str(name).strip().lower()
        if not key or key in seen:
            continue
        seen.add(key)
        area = lookup_math_area(key)
        if area is not None:
            resolved.append(area)
    return tuple(resolved)


def select_math_areas(
    prompt: str,
    *,
    limit: int = 12,
    include_all: bool = False,
) -> Tuple[Dict[str, Any], ...]:
    lowered = prompt.lower()
    scored = []
    for area in all_math_areas():
        score = 0
        area_name = str(area.get("name", "")).lower()
        if area_name and area_name in lowered:
            score += 8
        for term in area.get("extended_terms", area.get("terms", [])):
            term_text = str(term).lower()
            if term_text and term_text in lowered:
                score += 2 if " " in term_text else 1
        for domain in area.get("bridge_domains", []):
            if str(domain).lower() in lowered:
                score += 1
        scored.append((score, str(area.get("category", "")), area_name, area))

    ordered = tuple(
        item[-1]
        for item in sorted(scored, key=lambda item: (-item[0], item[1], item[2]))
    )
    if include_all:
        return ordered

    selected = tuple(item[-1] for item in scored if item[0] > 0)
    if selected:
        return tuple(
            item[-1]
            for item in sorted(
                (item for item in scored if item[0] > 0),
                key=lambda item: (-item[0], item[1], item[2]),
            )[:limit]
        )
    return ordered[:limit]
