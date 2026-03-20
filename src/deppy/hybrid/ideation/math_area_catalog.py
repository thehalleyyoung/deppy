"""Catalog of 500 mathematical areas for broad ideation search."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Iterable, Tuple


@dataclass(frozen=True)
class MathArea:
    key: str
    name: str
    category: str
    bridge_domains: Tuple[str, ...]
    keywords: Tuple[str, ...]


@dataclass(frozen=True)
class MathCategory:
    key: str
    name: str
    bridge_domains: Tuple[str, ...]
    keywords: Tuple[str, ...]
    area_keys: Tuple[str, ...]


_MATH_AREA_GROUPS = [
    (
        'abstract_algebra',
        ('category_theory', 'algebraic_geometry', 'type_theory'),
        ('algebra', 'structure', 'symmetry'),
        [
            'universal algebra',
            'semigroup theory',
            'monoid theory',
            'lattice theory',
            'Boolean algebras',
            'Jordan algebras',
            'Lie algebras',
            'associative algebras',
            'nonassociative algebras',
            'representation theory of algebras',
            'homological algebra',
            'algebraic K-theory',
            'homological dimensions',
            'tensor categories',
            'coalgebras and bialgebras',
            'Hopf algebras',
            'quantum groups',
            'invariant theory',
            'commutator theory',
            'operad theory',
        ],
    ),
    (
        'linear_algebra',
        ('machine_learning', 'software_engineering', 'category_theory'),
        ('matrix', 'tensor', 'operator'),
        [
            'matrix theory',
            'spectral theory',
            'multilinear algebra',
            'tensor decomposition',
            'numerical linear algebra',
            'convex geometry of matrices',
            'matrix inequalities',
            'low-rank approximation',
            'random matrix theory',
            'matrix manifolds',
            'operator pencils',
            'quadratic forms',
            'bilinear forms',
            'canonical forms',
            'matrix polynomials',
            'eigenvalue perturbation theory',
            'sparse linear algebra',
            'structured matrices',
            'tensor networks',
            'exterior algebra',
        ],
    ),
    (
        'group_theory',
        ('category_theory', 'algebraic_geometry', 'formal_verification'),
        ('group', 'symmetry', 'action'),
        [
            'finite group theory',
            'infinite group theory',
            'combinatorial group theory',
            'geometric group theory',
            'profinite groups',
            'permutation groups',
            'linear groups',
            'Lie groups',
            'Coxeter groups',
            'braid groups',
            'arithmetic groups',
            'growth of groups',
            'group cohomology',
            'group actions',
            'representation theory of groups',
            'character theory',
            'computational group theory',
            'subgroup growth',
            'amenable groups',
            'hyperbolic groups',
        ],
    ),
    (
        'ring_module_theory',
        ('algebraic_geometry', 'category_theory', 'type_theory'),
        ('ring', 'module', 'ideal'),
        [
            'commutative algebra',
            'noncommutative ring theory',
            'module theory',
            'ideal theory',
            'valuation theory',
            'homological methods in ring theory',
            'ring spectra',
            'local algebra',
            'Noetherian rings',
            'Artinian rings',
            'Prüfer domains',
            'Dedekind domains',
            'Krull domains',
            'Cohen-Macaulay modules',
            'Auslander-Reiten theory',
            'tilting theory',
            'Morita theory',
            'semisimple rings',
            'integral extensions',
            'graded ring theory',
        ],
    ),
    (
        'number_theory',
        ('algebraic_geometry', 'category_theory', 'formal_verification'),
        ('number', 'arithmetic', 'prime'),
        [
            'elementary number theory',
            'analytic number theory',
            'multiplicative number theory',
            'additive number theory',
            'Diophantine approximation',
            'Diophantine equations',
            'modular forms',
            'automorphic forms',
            'L-functions',
            'prime number theory',
            'sieve methods',
            'transcendental number theory',
            'p-adic number theory',
            'Iwasawa theory',
            'arithmetic combinatorics',
            'modular symbols',
            'class field theory',
            'arithmetic of elliptic curves',
            'local fields',
            'global fields',
        ],
    ),
    (
        'arithmetic_geometry',
        ('algebraic_geometry', 'category_theory', 'formal_verification'),
        ('arithmetic', 'scheme', 'cohomology'),
        [
            'arithmetic schemes',
            'Arakelov geometry',
            'p-adic Hodge theory',
            'motives',
            'Galois representations',
            'Shimura varieties',
            'rational points',
            'heights and canonical heights',
            'étale cohomology',
            'crystalline cohomology',
            'deformation theory of Galois representations',
            'moduli of abelian varieties',
            'arithmetic surfaces',
            'p-divisible groups',
            'anabelian geometry',
            'perfectoid spaces',
            'rigid cohomology',
            'Langlands program',
            'integral models',
            'Diophantine geometry',
        ],
    ),
    (
        'algebraic_geometry',
        ('algebraic_geometry', 'category_theory', 'type_theory'),
        ('scheme', 'sheaf', 'variety'),
        [
            'schemes',
            'sheaf cohomology',
            'derived algebraic geometry',
            'birational geometry',
            'moduli spaces',
            'intersection theory',
            'toric varieties',
            'singularity theory',
            'deformation theory',
            'stacks',
            'Hilbert schemes',
            'Quot schemes',
            'enumerative geometry',
            'Hodge theory',
            'cubic and quartic hypersurfaces',
            'abelian varieties',
            'algebraic surfaces',
            'complex projective varieties',
            'geometric invariant theory',
            'mirror symmetry',
        ],
    ),
    (
        'differential_geometry',
        ('algebraic_geometry', 'category_theory', 'formal_verification'),
        ('curvature', 'manifold', 'geodesic'),
        [
            'Riemannian geometry',
            'pseudo-Riemannian geometry',
            'affine differential geometry',
            'curvature flows',
            'minimal surface theory',
            'gauge theory',
            'spin geometry',
            'submanifold geometry',
            'geometric analysis',
            'geometric measure theory',
            'foliation theory',
            'calibration geometry',
            'geometric quantization',
            'Cartan geometry',
            'Finsler geometry',
            'information geometry',
            'integral geometry',
            'global differential geometry',
            'local differential geometry',
            'holonomy theory',
        ],
    ),
    (
        'symplectic_contact_geometry',
        ('algebraic_geometry', 'category_theory', 'machine_learning'),
        ('symplectic', 'Hamiltonian', 'Poisson'),
        [
            'symplectic manifolds',
            'contact manifolds',
            'Poisson geometry',
            'Hamiltonian dynamics',
            'symplectic topology',
            'Floer homology',
            'Fukaya categories',
            'moment maps',
            'integrable systems',
            'contact homology',
            'symplectic field theory',
            'Lagrangian intersections',
            'mirror symmetry for symplectic geometry',
            'Kähler geometry',
            'Sasakian geometry',
            'multisymplectic geometry',
            'Jacobi geometry',
            'geometric mechanics',
            'symplectic reduction',
            'geometric control',
        ],
    ),
    (
        'topology',
        ('category_theory', 'algebraic_geometry', 'type_theory'),
        ('topology', 'space', 'continuity'),
        [
            'point-set topology',
            'continuum theory',
            'compactifications',
            'dimension theory',
            'topology of function spaces',
            'topological groups',
            'topological dynamics',
            'descriptive set theory',
            'topological lattices',
            'shape theory',
            'proximity spaces',
            'locale theory',
            'domain theory',
            'convergence spaces',
            'set-theoretic topology',
            'topological game theory',
            'hyperspace topology',
            'compactly generated spaces',
            'uniform spaces',
            'continuity spaces',
        ],
    ),
    (
        'algebraic_topology',
        ('category_theory', 'type_theory', 'formal_verification'),
        ('homotopy', 'cohomology', 'spectrum'),
        [
            'homotopy theory',
            'homology theory',
            'cohomology operations',
            'stable homotopy theory',
            'spectra',
            'equivariant homotopy theory',
            'obstruction theory',
            'higher topos theory',
            'model categories',
            'simplicial sets',
            'simplicial complexes',
            'homotopical algebra',
            'generalized cohomology',
            'topological K-theory',
            'cobordism theory',
            'persistent homology',
            'homotopy type theory',
            'rational homotopy theory',
            'chromatic homotopy theory',
            'string topology',
        ],
    ),
    (
        'geometric_topology',
        ('category_theory', 'algebraic_geometry', 'formal_verification'),
        ('manifold', 'knot', 'embedding'),
        [
            'knot theory',
            'low-dimensional topology',
            '3-manifold theory',
            '4-manifold theory',
            'mapping class groups',
            'Teichmüller theory',
            'hyperbolic manifolds',
            'contact topology',
            'topological quantum field theory',
            'braid topology',
            'foliated manifolds',
            'surgery theory',
            'handlebody theory',
            'PL topology',
            'embeddings and immersions',
            'manifold invariants',
            'link homologies',
            'quantum invariants of manifolds',
            'concordance theory',
            'geometric structures on manifolds',
        ],
    ),
    (
        'real_analysis',
        ('formal_verification', 'machine_learning', 'software_engineering'),
        ('measure', 'variation', 'estimate'),
        [
            'measure theory',
            'integration theory',
            'geometric integration',
            'real-variable methods',
            'differentiation theory',
            'absolute continuity',
            'functions of bounded variation',
            'Fourier series',
            'fractal analysis',
            'singular integrals',
            'ergodic theory',
            'nonlinear analysis',
            'potential theory',
            'convex analysis',
            'monotone operator theory',
            'Sobolev spaces',
            'variational methods',
            'free boundary problems',
            'calculus of variations',
            'nonsmooth analysis',
        ],
    ),
    (
        'complex_analysis',
        ('algebraic_geometry', 'category_theory', 'machine_learning'),
        ('holomorphic', 'complex', 'analytic'),
        [
            'one complex variable',
            'several complex variables',
            'complex manifolds',
            'analytic spaces',
            'meromorphic functions',
            'Nevanlinna theory',
            'complex dynamics',
            'conformal mapping',
            'quasiconformal maps',
            'Riemann surfaces',
            'Teichmüller spaces',
            'complex differential equations',
            'plurisubharmonic functions',
            'CR geometry',
            'Bergman kernels',
            'Hardy spaces',
            'holomorphic foliations',
            'value distribution theory',
            'complex potential theory',
            'asymptotic analysis of analytic functions',
        ],
    ),
    (
        'functional_analysis',
        ('formal_verification', 'machine_learning', 'software_engineering'),
        ('operator', 'Banach', 'Hilbert'),
        [
            'Banach spaces',
            'Hilbert spaces',
            'locally convex spaces',
            'topological vector spaces',
            'operator theory',
            'operator algebras',
            'C*-algebras',
            'von Neumann algebras',
            'noncommutative geometry',
            'semigroup theory of operators',
            'fixed point theory',
            'frame theory',
            'interpolation spaces',
            'distribution theory',
            'rigged Hilbert spaces',
            'measure algebras',
            'Banach lattices',
            'nonlocal operators',
            'free probability',
            'quantum functional analysis',
        ],
    ),
    (
        'harmonic_analysis',
        ('machine_learning', 'software_engineering', 'formal_verification'),
        ('Fourier', 'wavelet', 'frequency'),
        [
            'abstract harmonic analysis',
            'Fourier analysis',
            'wavelet analysis',
            'time-frequency analysis',
            'representation-theoretic harmonic analysis',
            'Calderón-Zygmund theory',
            'restriction theory',
            'oscillatory integrals',
            'pseudo-differential operators',
            'microlocal analysis',
            'uncertainty principles',
            'signal decomposition',
            'sparse domination',
            'multilinear harmonic analysis',
            'spectral multipliers',
            'sampling theory',
            'Gabor analysis',
            'harmonic analysis on groups',
            'harmonic analysis on manifolds',
            'dispersive estimates',
        ],
    ),
    (
        'partial_differential_equations',
        ('machine_learning', 'formal_verification', 'software_engineering'),
        ('PDE', 'equation', 'boundary'),
        [
            'elliptic PDE',
            'parabolic PDE',
            'hyperbolic PDE',
            'nonlinear PDE',
            'stochastic PDE',
            'conservation laws',
            'reaction-diffusion equations',
            'Navier-Stokes equations',
            'Euler equations',
            'Schrödinger equations',
            'wave equations',
            'kinetic equations',
            'transport equations',
            'homogenization',
            'inverse problems for PDE',
            'control of PDE',
            'mean field games',
            'viscosity solutions',
            'regularity theory',
            'boundary layer analysis',
        ],
    ),
    (
        'dynamical_systems',
        ('machine_learning', 'formal_verification', 'software_engineering'),
        ('dynamics', 'orbit', 'stability'),
        [
            'ordinary differential equations',
            'bifurcation theory',
            'chaos theory',
            'ergodic dynamical systems',
            'symbolic dynamics',
            'topological dynamics',
            'smooth dynamical systems',
            'celestial mechanics',
            'Hamiltonian systems',
            'stochastic dynamics',
            'random dynamical systems',
            'population dynamics',
            'epidemiological dynamics',
            'complex systems',
            'delay differential equations',
            'hybrid dynamical systems',
            'invariant manifolds',
            'metastability',
            'time-series dynamics',
            'control dynamical systems',
        ],
    ),
    (
        'probability',
        ('machine_learning', 'formal_verification', 'software_engineering'),
        ('probability', 'stochastic', 'uncertainty'),
        [
            'measure-theoretic probability',
            'stochastic processes',
            'martingale theory',
            'stochastic calculus',
            'Brownian motion',
            'Lévy processes',
            'random walks',
            'percolation theory',
            'interacting particle systems',
            'concentration inequalities',
            'large deviations',
            'random graphs',
            'probabilistic combinatorics',
            'stochastic control',
            'rough paths',
            'branching processes',
            'queueing theory',
            'Bayesian probability',
            'financial mathematics',
            'uncertainty quantification',
        ],
    ),
    (
        'statistics',
        ('machine_learning', 'software_engineering', 'formal_verification'),
        ('statistics', 'inference', 'estimation'),
        [
            'statistical inference',
            'Bayesian statistics',
            'nonparametric statistics',
            'robust statistics',
            'experimental design',
            'causal inference',
            'survival analysis',
            'high-dimensional statistics',
            'time series analysis',
            'multivariate analysis',
            'spatial statistics',
            'stochastic volatility modeling',
            'statistical learning theory',
            'information geometry',
            'empirical process theory',
            'resampling methods',
            'sequential analysis',
            'network statistics',
            'uncertainty calibration',
            'topological data analysis',
        ],
    ),
    (
        'combinatorics',
        ('category_theory', 'formal_verification', 'machine_learning'),
        ('combinatorics', 'counting', 'extremal'),
        [
            'enumerative combinatorics',
            'extremal combinatorics',
            'additive combinatorics',
            'probabilistic combinatorics',
            'algebraic combinatorics',
            'combinatorial design theory',
            'matroid theory',
            'partition theory',
            'Ramsey theory',
            'combinatorics on words',
            'poset theory',
            'generating functions',
            'combinatorial species',
            'coding theory',
            'finite geometry',
            'polyhedral combinatorics',
            'tableaux and symmetric functions',
            'combinatorial optimization',
            'cluster combinatorics',
            'discrete geometry',
        ],
    ),
    (
        'graph_theory_discrete_math',
        ('software_engineering', 'machine_learning', 'formal_verification'),
        ('graph', 'network', 'discrete'),
        [
            'graph coloring',
            'spectral graph theory',
            'extremal graph theory',
            'random graphs',
            'graph algorithms',
            'network flows',
            'matching theory',
            'graph minors',
            'hypergraph theory',
            'expander graphs',
            'topological graph theory',
            'geometric graph theory',
            'domination theory',
            'graph limits',
            'distributed graph algorithms',
            'finite automata',
            'discrete algorithms',
            'Boolean function analysis',
            'error-correcting codes',
            'discrete probability',
        ],
    ),
    (
        'logic_foundations',
        ('type_theory', 'formal_verification', 'category_theory'),
        ('logic', 'proof', 'foundations'),
        [
            'set theory',
            'model theory',
            'recursion theory',
            'computability theory',
            'proof theory',
            'intuitionistic logic',
            'modal logic',
            'temporal logic',
            'constructive mathematics',
            'ordinal analysis',
            'reverse mathematics',
            'proof complexity',
            'finite model theory',
            'descriptive complexity',
            'forcing and independence',
            'large cardinals',
            'inner model theory',
            'realizability',
            'formal semantics',
            'foundations of mathematics',
        ],
    ),
    (
        'category_type_theory',
        ('category_theory', 'type_theory', 'formal_verification'),
        ('category', 'type', 'descent'),
        [
            'category theory',
            'enriched category theory',
            'higher category theory',
            'topos theory',
            'categorical logic',
            'monoidal categories',
            'sheaf theory',
            'descent theory',
            'type theory',
            'dependent type theory',
            'homotopy type theory',
            'cubical type theory',
            'proof assistants',
            'program semantics',
            'lambda calculus',
            'linear type theory',
            'synthetic differential geometry',
            'coalgebra',
            'operads and higher operads',
            'rewriting systems',
        ],
    ),
    (
        'optimization_numerical_analysis',
        ('machine_learning', 'software_engineering', 'formal_verification'),
        ('optimization', 'numerical', 'computation'),
        [
            'numerical analysis',
            'finite element methods',
            'finite difference methods',
            'spectral methods',
            'numerical linear algebra',
            'optimization theory',
            'convex optimization',
            'nonconvex optimization',
            'stochastic optimization',
            'integer optimization',
            'semidefinite programming',
            'optimal transport',
            'numerical PDE',
            'adaptive mesh refinement',
            'surrogate modeling',
            'Bayesian optimization',
            'gradient flows',
            'automatic differentiation',
            'computational geometry',
            'scientific computing',
        ],
    ),
]


def _keywords_for(category: str, area: str, group_keywords: Tuple[str, ...]) -> Tuple[str, ...]:
    tokens = {
        token
        for token in (category + " " + area).lower().replace("-", " ").replace("/", " ").split()
        if len(token) >= 3
    }
    tokens.add(area.lower())
    tokens.add(category.replace("_", " "))
    tokens.update(keyword.lower() for keyword in group_keywords)
    return tuple(sorted(tokens))


def _build_catalog() -> Tuple[MathArea, ...]:
    entries = []
    for category, bridges, group_keywords, areas in _MATH_AREA_GROUPS:
        for area in areas:
            entries.append(
                MathArea(
                    key=f"{category}__{_normalize(area)}",
                    name=area,
                    category=category,
                    bridge_domains=tuple(bridges),
                    keywords=_keywords_for(category, area, tuple(group_keywords)),
                )
            )
    if len(entries) != 500:
        raise AssertionError(f"Expected 500 math areas, found {len(entries)}")
    return tuple(entries)


def _normalize(text: str) -> str:
    cleaned = "".join(ch.lower() if ch.isalnum() else "_" for ch in text)
    while "__" in cleaned:
        cleaned = cleaned.replace("__", "_")
    return cleaned.strip("_")


ALL_MATH_AREAS: Tuple[MathArea, ...] = _build_catalog()
MATH_AREA_INDEX: Dict[str, MathArea] = {area.key: area for area in ALL_MATH_AREAS}


def _build_category_index() -> Dict[str, MathCategory]:
    categories: Dict[str, MathCategory] = {}
    for category, bridges, group_keywords, areas in _MATH_AREA_GROUPS:
        area_keys = tuple(f"{category}__{_normalize(area)}" for area in areas)
        keywords = tuple(
            sorted(
                {
                    category.replace("_", " "),
                    *[keyword.lower() for keyword in group_keywords],
                    *[area.lower() for area in areas],
                }
            )
        )
        categories[category] = MathCategory(
            key=category,
            name=category.replace("_", " "),
            bridge_domains=tuple(bridges),
            keywords=keywords,
            area_keys=area_keys,
        )
    return categories


MATH_CATEGORY_INDEX: Dict[str, MathCategory] = _build_category_index()


def _build_term_index() -> Dict[str, Tuple[str, ...]]:
    term_map: Dict[str, set[str]] = {}
    for area in ALL_MATH_AREAS:
        for term in area.keywords:
            term_map.setdefault(term, set()).add(area.key)
    for category in MATH_CATEGORY_INDEX.values():
        for term in category.keywords:
            term_map.setdefault(term, set()).update(category.area_keys)
    return {
        term: tuple(sorted(area_keys))
        for term, area_keys in sorted(term_map.items())
    }


MATH_TERM_INDEX: Dict[str, Tuple[str, ...]] = _build_term_index()
ALL_MATH_TERMS: Tuple[str, ...] = tuple(MATH_TERM_INDEX.keys())
MATH_ONTOLOGY = {
    "root": "mathematics",
    "category_count": len(MATH_CATEGORY_INDEX),
    "area_count": len(ALL_MATH_AREAS),
    "term_count": len(ALL_MATH_TERMS),
    "categories": tuple(
        {
            "key": category.key,
            "name": category.name,
            "bridge_domains": category.bridge_domains,
            "keywords": category.keywords,
            "area_keys": category.area_keys,
        }
        for category in MATH_CATEGORY_INDEX.values()
    ),
}


def select_math_areas(prompt: str, *, limit: int = 12, include_all: bool = False) -> Tuple[MathArea, ...]:
    lowered = prompt.lower()
    scored = []
    for area in ALL_MATH_AREAS:
        score = 0
        if area.name.lower() in lowered:
            score += 5
        for keyword in area.keywords:
            if keyword in lowered:
                score += 1
        if any(domain in lowered for domain in area.bridge_domains):
            score += 1
        scored.append((score, area.category, area.name, area))
    ordered = tuple(item[-1] for item in sorted(scored, key=lambda item: (-item[0], item[1], item[2])))
    if include_all:
        return ordered
    selected = tuple(area for area in ordered if any(keyword in lowered for keyword in area.keywords))
    if selected:
        return selected[:limit]
    return ordered[:limit]


def bridge_domains_for(areas: Iterable[MathArea]) -> Tuple[str, ...]:
    ordered = []
    seen = set()
    for area in areas:
        for domain in area.bridge_domains:
            if domain not in seen:
                seen.add(domain)
                ordered.append(domain)
    return tuple(ordered)
