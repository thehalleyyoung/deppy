# Direction I — Sheaf-Descent Semantic Typing: Global Types as Glued Sections of Local Evidence

## Executive thesis


This direction rewrites the monograph around a genuinely different answer to the question “what is a type?” A type is not a bag of weighted predicates selected by optimization. Instead, a type is a global semantic section obtained by gluing together local judgments defined over a cover of observational sites: syntax sites, control-flow sites, dynamic-trace sites, library-trigger sites, interprocedural summary sites, and proof-certificate sites. The dramatic advantage is that minimal annotation stops meaning “manually write fewer clauses” and starts meaning “supply the fewest boundary conditions needed to eliminate global ambiguity.” Maximum information then becomes a local-to-global extension problem: infer as rich a global section as possible subject to consistency on overlaps, descent data, and decidable local theories.

In that world, proofs of algorithmic correctness and low-annotation refinement typing are no longer two separate products awkwardly forced into one pipeline. They become two kinds of local evidence living on different regions of the same site. A correctness proof contributes transport maps, cocycles, or descent witnesses. A Torch trace, shape operation, or indexing pattern contributes local semantic sections over tensor-theoretic sites. The central optimization problem is no longer simply “choose clauses,” but “choose the most informative globally glueable section under sparse user seeding and bounded local proof obligations.”


## Why this would require a complete rewrite of `dependent_typing_as_optimization.tex`


The current monograph already pushes beyond ordinary refinement typing by treating maximal type information as an optimization problem. The radical move here is to say that the optimization variable should not be a subset of candidate atoms at all. It should be a structured global section in a sheaf-like object whose stalks carry decidable local semantics. That changes almost every chapter. Candidate generation becomes cover synthesis. Residual goals become cohomological obstructions or failed descent conditions. Proof reuse becomes transport across overlaps. Interprocedural reasoning becomes functorial restriction and reindexing. Theory packs stop being flat sources of clauses and instead become factories for new sites, local sections, and compatibility maps.



The slogan “minimal annotation, maximum information” becomes mathematically precise: the user provides a sparse seed section, or perhaps only a few marked boundary values, and the system solves a constrained extension problem. If the extension is unique, the user wrote the minimum amount of semantic text necessary. If multiple extensions remain, the system reports the obstruction classes that distinguish them and asks only for annotations that resolve those classes. This is much more radical than asking which predicates should be retained in a MaxSMT frontier, because it changes the unit of information from isolated propositions to global consistency structure.


## Signature mathematical kernel


Let $\mathcal{S}$ be a category of observation sites generated from a program: objects are regions such as function bodies, CFG blocks, SSA values, library-trigger neighborhoods, dynamic trace windows, proof modules, and interprocedural summaries; morphisms are restriction or reindexing maps. Let $\mathsf{Sem}: \mathcal{S}^{op} \to \mathsf{Poset}$ be a presheaf assigning to each site a poset of local semantic sections. A dependent type for a term $e$ is a compatible family $\sigma \in \Gamma(U, \mathsf{Sem})$ on a cover $U = \{U_i\}$ such that

$$\forall i,j.\; \sigma_i|_{U_i \cap U_j} = \sigma_j|_{U_i \cap U_j},$$

together with a proof-boundary map $\beta(\sigma_i)$ assigning each local clause to a trusted-automatic, bounded-automatic, or residual fragment. Minimal annotation is the problem of finding a seed family $a$ of minimal cost such that the extension set

$$\mathrm{Ext}(a) = \{\sigma \mid \sigma \text{ extends } a \text{ and satisfies descent}\}$$

is either singleton or has maximal information score under a partial order on sections. Obstructions to unique extension are modeled by nontrivial descent defects or, in the more ambitious version, by cohomology classes associated with the site cover.


## Foundational primitives

The current monograph treats type information as a weighted collection of atoms packed by an optimization layer. Each primitive below instead changes what a type is, how evidence is aggregated, and why very small annotations can unlock much richer global semantics.

### Primitive 1: Observation site categories

**Core move.** Instead of a single global inference state, the program is decomposed into a category of sites capturing syntax, control-flow, dynamic traces, library calls, proof modules, and interprocedural summaries. Each site represents a region where local semantics can be checked cheaply and independently before gluing.

**Formal object.** The site category should include explicit restriction maps from whole functions to SSA values, from proof modules to referenced terms, from Torch operations to operand/result neighborhoods, and from dynamic traces to the corresponding symbolic regions. The cover itself becomes a first-class output of analysis.

**Minimal-annotation consequence.** Sparse user annotations become seeds attached to only a few sites. The system should then infer whether the rest of the cover is forced by descent. This makes annotation cost depend on how many ambiguity classes remain after local inference, not on how many clauses happen to be useful globally.

**Algorithmic and library consequence.** Torch theory packs can add or refine sites instead of merely adding facts. A `torch.sort` call can create order sites, permutation sites, and index sites with explicit overlap structure, making it possible to recover richer downstream semantics automatically.

**Why this is more radical than the current monograph.** The current monograph optimizes over candidate atoms in one semantic signature. This proposal says the signature is secondary; the primary object is the covered semantic site from which signatures are extracted as views.

### Primitive 2: Stalk theories with decidable local logics

**Core move.** Every site carries its own small logic, or stalk theory, chosen to be expressive enough for that neighborhood but still cheap enough to solve automatically. Tensor shape equalities, sortedness witnesses, linear arithmetic, protocol obligations, and heap facts need not live in one undifferentiated logic.

**Formal object.** Mathematically this is a presheaf valued in posets, semilattices, or certified local proof states. Each stalk theory exports admissible predicates, witness forms, and a local boundary classifier. Restriction maps translate facts between adjacent stalks while preserving soundness and provenance.

**Minimal-annotation consequence.** A user or LLM does not need to know the whole logical stack. They only need to provide facts in the stalk where ambiguity survives. The system can often infer which stalk matters by tracing where descent fails.

**Algorithmic and library consequence.** For Torch, shape and indexing sites can stay in compact semialgebraic fragments while order or permutation sites use a different local solver. This helps automation because rich global behavior is built from small local kernels.

**Why this is more radical than the current monograph.** The current monograph already stratifies proof boundaries, but the unit of stratification is still a proposition. Here the unit is a site-specific semantic calculus.

### Primitive 3: Presheaf of semantic sections

**Core move.** A type judgment becomes a local section in a presheaf of semantic states rather than a flat tuple of clauses. That means semantic information can be restricted, extended, and compared geometrically rather than only by subset inclusion.

**Formal object.** For each site $U$, the presheaf assigns a poset of admissible local dependent contracts, witness carriers, and proof statuses. Restriction maps carry local contracts from larger sites to smaller ones. The structure supports a precise notion of information growth: one section refines another if it lies lower in the ambiguity order and higher in the semantic-information order.

**Minimal-annotation consequence.** Minimal annotation becomes minimal forcing data for a section extension problem. That is radically stronger than asking for the smallest set of user clauses because the forcing data can include examples, loop summaries, proof fragments, or marked relationships between sites.

**Algorithmic and library consequence.** Program transformations such as wrapper introduction, aliasing, or local binding no longer destroy meaning just because the textual shape changes. If the same section restricts to the same local sites, the semantics should be preserved automatically.

**Why this is more radical than the current monograph.** The current monograph treats propagation as transport of atoms. The sheaf design treats propagation as restriction and extension of sections.

### Primitive 4: Descent data as the real core of typing

**Core move.** The central invariant is no longer just that facts hold; it is that families of local facts agree on overlaps. This turns many fragile inference heuristics into principled descent conditions.

**Formal object.** Each overlap site $U_i \cap U_j$ carries compatibility equations. A global type exists only when local sections satisfy those equations. The typing engine is therefore a descent solver, and failure explains not only that something is missing, but where the incompatibility sits in the cover.

**Minimal-annotation consequence.** User guidance is requested only when multiple non-isomorphic glueings remain or when a compatibility equation cannot be discharged automatically. The annotation the system asks for is therefore structural and sharply targeted.

**Algorithmic and library consequence.** Torch pipelines that mix shape changes, views, and index projections become much more robust because the semantics of downstream sites must agree with imported upstream sections. This gives a principled explanation for why nested operations should still preserve information.

**Why this is more radical than the current monograph.** The current monograph uses repair suggestions after optimization. This proposal internalizes repair as a failure of descent.

### Primitive 5: Cohomological obstructions as a model of missing information

**Core move.** When local evidence does not glue uniquely, the ambiguity should not just be reported as “residual goals remain.” It should be analyzed as an obstruction class measuring which global distinctions cannot be resolved from current evidence.

**Formal object.** The bold version uses Čech-style obstruction classes or an equivalent combinatorial invariant on the cover. The obstruction need not be full-blown algebraic topology in implementation, but the mathematical story should be that unresolved global semantics correspond to nontrivial cocycles.

**Minimal-annotation consequence.** This is perhaps the sharpest possible interpretation of minimal annotation. The ideal system asks for exactly the annotation that resolves the obstruction class. In other words, the tool should request the minimum semantic intervention required to force a unique or maximally informative global section.

**Algorithmic and library consequence.** For algorithms, the missing object might be a loop invariant or a permutation witness. For Torch code, it might be the relationship between an index tensor and a sorted result. The same obstruction language can describe both.

**Why this is more radical than the current monograph.** The current monograph already talks about residuals and repair. Obstruction classes would provide a far more radical and mathematically coherent semantics for why residuals exist.

### Primitive 6: Proof-carrying transport maps

**Core move.** A proof should not be a static annotation pasted onto a function. It should be a transport artifact showing how semantics move between sites or covers. That makes proofs compositional in a stronger sense than mere theorem reuse.

**Formal object.** Each proof module contributes explicit morphisms or commuting diagrams between local sections. For recursive algorithms this could mean transport along inductive decomposition; for Torch operators it could mean transport from sort semantics to downstream index semantics or from view semantics to alias-preservation lemmas.

**Minimal-annotation consequence.** Minimal proof annotation becomes “state only the non-obvious transport law.” A proof-oriented user can pin a powerful map once, and ordinary users then inherit the consequence through descent without ever seeing the proof object.

**Algorithmic and library consequence.** This would let algorithmic correctness theorems and mundane library typing share infrastructure. The sorting proof and the tensor refinement are not separate worlds; they are transport sources within the same global object.

**Why this is more radical than the current monograph.** The present monograph allows proofs to add explicit facts. The rewrite would let proofs reshape the extension space itself.

### Primitive 7: Dynamic trace refinement as site contraction

**Core move.** Dynamic evidence should not merely attach extra predicates after the fact. It should contract the admissible local sections on trace-visible sites, thereby narrowing the global section space in a principled way.

**Formal object.** If a trace observes a runtime guard, shape relation, or successful assertion, the corresponding site is refined by intersection with the observed section subset. Re-running descent then propagates the new information globally while preserving the distinction between empirical evidence and theorem-level proof.

**Minimal-annotation consequence.** This gives a beautiful minimal-annotation story for ordinary users: write the program, maybe run a representative example, and let traces remove entire ambiguity classes before asking the user for any symbolic annotation.

**Algorithmic and library consequence.** Torch programs benefit immediately because many tensor facts are cheaply observed on representative executions: ranks, view compatibility, index shape agreements, and monotonicity surrogates can all become local trace constraints.

**Why this is more radical than the current monograph.** The current monograph is already evidence-aware, but a sheaf semantics would make dynamic evidence a natural operation on the type object rather than an ad hoc source of candidates.

### Primitive 8: Library covers rather than flat theory packs

**Core move.** Library theories should generate covers and compatibility maps, not just atoms. A theory pack becomes a constructor for a semantic micro-topology around certain program patterns.

**Formal object.** For `torch.sort`, the pack should create order, permutation, index, and alias sites with defined overlaps. For data structures or algorithms, packs should create sites for heap shape, ranking functions, amortized potential, or graph reachability facts.

**Minimal-annotation consequence.** Once theory packs create covers, minimal annotation improves because the user benefits from the library’s own decomposition of semantic structure. They no longer have to manually coordinate facts that the theory pack knows are linked.

**Algorithmic and library consequence.** This would make nested or aliased operations much easier to support. The cover is semantic, not merely textual, so the theory survives code motion, wrappers, and local binding patterns.

**Why this is more radical than the current monograph.** The current monograph treats theory packs as candidate generators. The rewrite treats them as geometry generators.

### Primitive 9: Algorithm proof sheaves

**Core move.** Classical correctness arguments for sorting, shortest paths, graph traversal, and data-structure maintenance can be encoded as sheaves of local invariants that glue across recursion, iteration, and helper decomposition.

**Formal object.** Instead of a single theorem statement at the boundary of a function, each algorithm induces local theorem sites: loop-body sites, variant sites, partition sites, witness sites, and summary sites. The correctness claim is recovered by descent through these proof-local sections.

**Minimal-annotation consequence.** A human or LLM proof author can therefore work locally. They state only the nontrivial invariant or transport law, and the system distributes its consequence globally. This is the exact behavior we want from a minimum-annotation proof surface.

**Algorithmic and library consequence.** The dream implementation would finally mix proof-first algorithm verification with ordinary refinement typing without making one feel like a bolted-on special case of the other.

**Why this is more radical than the current monograph.** The current monograph points toward this integration, but the sheaf formulation would make it mathematically first-class.

## How proofs of algorithmic correctness and refinement typing would coexist


Correctness proofs of algorithms fit naturally into this picture because most algorithm proofs are already local-to-global arguments: loop invariants, recursion lemmas, permutation witnesses, and data-structure invariants all live locally and must be transported consistently across a decomposition of the program. In the rewritten monograph, a proof term is not merely a justification attached to a proposition; it is descent data explaining why families of local propositions are coherent under restriction. That means an algorithm proof can improve ordinary typing not just by adding one more theorem, but by shrinking the space of possible global sections everywhere its transport maps apply.

This also gives a new story for proof reuse. A sorting proof should not merely prove `sorted(result)` once. It should establish a local section over the sorting site and a transport law for wrappers, views, slices, and index projections. Then a later Torch pipeline that consumes a sorted tensor inherits structure because those sites overlap, not because a human restated the exact same contract on every function.



Torch programs become especially compelling because tensor semantics are inherently local-to-global. Shape operations, index projections, permutation information, monotonicity facts, and value-identity facts all appear in different neighborhoods of the program. A sheaf-style design allows each neighborhood to carry a small decidable local theory. The system can then glue together shape sections, indexing sections, and order-theoretic sections while keeping proof obligations local. Dynamic refinement typing slots in as trace-induced refinement of sites: a runtime observation does not overwrite the type; it shrinks the admissible local sections on the affected sites and therefore narrows the global extension set.


## Theorem agenda

A serious rewrite needs a theorem program substantial enough to justify the new mathematics. The point is not to throw abstract language at the problem; the point is to define new objects that yield better automation, better compression of annotation, and a cleaner interface between proofs and ordinary code.

### Theorem target 1: Local soundness and gluing soundness

**Statement shape.** Show that if every local stalk proof system is sound and every restriction map preserves validity, then any descended global section is sound as a dependent contract for the enclosing program region.

**Why it matters.** This theorem licenses aggressive local automation because the global contract inherits soundness from the local theories and compatibility maps rather than requiring a monolithic global solver.

**Likely proof strategy.** The proof should proceed by induction over the site cover and use commutation of restrictions with local verification, followed by a descent argument that any glued section respects every overlap judgment.

### Theorem target 2: Descent completeness under acyclic covers

**Statement shape.** Prove that under an acyclic or suitably tame cover, global semantic sections are completely characterized by local sections plus overlap compatibility constraints.

**Why it matters.** This tells us when the sheaf machinery buys true automation rather than merely new language. In acyclic regimes, no hidden global information is lost by solving locally and gluing.

**Likely proof strategy.** The likely proof uses standard descent-completeness arguments adapted to the chosen semantic category, possibly with a discrete Čech argument rather than full topos machinery.

### Theorem target 3: Minimal seed theorem

**Statement shape.** Characterize the smallest-cost family of annotations that forces a unique global extension up to semantic equivalence.

**Why it matters.** This is the mathematical heart of the minimal-annotation slogan. The theorem would let the tool explain that a specific annotation is not just useful but optimal relative to the ambiguity structure of the current cover.

**Likely proof strategy.** One route is to define a forcing rank on seed families and prove that ambiguity classes collapse monotonically under seed refinement, yielding a minimal hitting-set or lattice-basis characterization.

### Theorem target 4: Obstruction monotonicity

**Statement shape.** Show that adding valid local evidence, new library sites, or proof transport maps can only reduce the space of obstruction classes, never create spurious new ambiguity that was absent before.

**Why it matters.** This gives a principled notion of monotone theory growth and makes it possible to reason about why adding a new pack should only improve information.

**Likely proof strategy.** The proof should use monotonicity of extension sets under refinement of the presheaf and functoriality of the associated obstruction invariant.

### Theorem target 5: Proof transport conservativity

**Statement shape.** Prove that imported proof maps refine the extension space only through the explicit transport law they encode and cannot silently inject arbitrary global facts.

**Why it matters.** This protects the trust boundary and keeps proof-first usage compatible with minimal annotation for ordinary users.

**Likely proof strategy.** The key step is to show that proof-induced restrictions factor through declared morphisms and are themselves checked in a trusted kernel or bounded fragment.

### Theorem target 6: Interprocedural Beck–Chevalley property

**Statement shape.** Formalize and prove a square-commutation law stating that restriction along call boundaries and gluing along wrapper structure commute whenever the wrapper is semantically transparent.

**Why it matters.** This theorem would justify alias-forwarding propagation, wrapper transparency, and richer interprocedural reuse as consequences of the site semantics rather than special-case heuristics.

**Likely proof strategy.** Expect a categorical proof over pullback squares induced by call/return boundaries, specialized to the implemented site category.

### Theorem target 7: Torch cover composition theorem

**Statement shape.** Show that shape, indexing, order, and alias sites created by Torch theory packs compose conservatively, so gluing one pack’s sections into another’s never invents unsupported semantics.

**Why it matters.** This theorem is what would let the monograph claim deep cross-pack semantics with a straight face.

**Likely proof strategy.** Likely a local conservativity argument over overlap sites, plus proof that the joint cover refines the original site decomposition without changing verified local truth.

### Theorem target 8: Annotation compression bound

**Statement shape.** Bound the number or cost of user annotations needed in terms of the rank of unresolved obstruction classes rather than the raw number of desired predicates.

**Why it matters.** This would finally turn “maximum information from minimal annotation” into a theorem-like claim instead of a design aspiration.

**Likely proof strategy.** The argument could proceed through a basis theorem for ambiguity classes together with a cost model on admissible seeds.

## Algorithmic realization

Each direction needs an implementation story that turns the mathematics into something a user can actually run on PyTorch and ordinary Python. The goal is still minimal annotation, but the mechanism is now deeper: every algorithm below is designed to convert weak observational evidence and sparse user hints into high-information contracts.

### Algorithm family 1: Cover synthesis from program structure and traces

**Main procedure.** Build the observation site category automatically from AST regions, CFG blocks, SSA values, library-call neighborhoods, proof declarations, and optional runtime traces. Infer overlaps from shared symbolic variables, control dependencies, and known library transport rules.

**Why it helps minimal annotation.** A strong cover immediately reduces annotation demand because the system knows where information can be inferred structurally. The user is not asked for a global contract if the cover geometry already determines it.

**Decidable-core strategy.** Every site constructor must declare a local fragment and a projection into the kernel vocabulary. The implementation can therefore remain staged: rich cover first, decidable local solving second.

**Implementation implication.** This would replace a large part of current candidate harvesting and would likely sit between surface lowering and semantic optimization.

### Algorithm family 2: Local stalk solver orchestration

**Main procedure.** Run the right solver per site: linear arithmetic on numeric sites, semialgebraic shape reasoning on tensor-shape sites, finite witness enumeration on permutation-index sites, and kernel proof checking on proof-transport sites.

**Why it helps minimal annotation.** Because each solver works on a small neighborhood, automation can become much stronger before the user is asked to intervene.

**Decidable-core strategy.** Decidability is maintained locally even if the global object is richer than any single solver could handle monolithically.

**Implementation implication.** The present proof-boundary layer becomes a site-level scheduler rather than only a per-atom classifier.

### Algorithm family 3: Descent solver with obstruction extraction

**Main procedure.** After local solving, run a global compatibility engine that attempts to glue the local sections and, on failure, computes explicit overlap conflicts or basis obstructions.

**Why it helps minimal annotation.** This is the machine that turns mathematical elegance into real user experience. Instead of vague residuals, the tool can ask for the one invariant or proof transport needed to resolve the obstruction.

**Decidable-core strategy.** The glueing engine can stay combinatorial, with only local theorem checks delegated to solvers or proof kernels.

**Implementation implication.** This subsystem would largely replace today’s residual-goal and repair-report story.

### Algorithm family 4: Proof transport import and compilation

**Main procedure.** Compile proof-surface declarations into transport maps over sites, verify them in the kernel or bounded solver layer, and register them as admissible morphisms for future gluing.

**Why it helps minimal annotation.** A single proof artifact can now reduce annotation demand across many functions because it changes how sections travel across the cover.

**Decidable-core strategy.** Transport compilation should output only site-local proof obligations, so the kernel never needs the full global object in one shot.

**Implementation implication.** The current proof surface would need to become more explicitly about maps, invariants, and compatibility lemmas.

### Algorithm family 5: Dynamic site contraction and replay

**Main procedure.** Run instrumented programs or replay traces, contract the admissible local sections on observed sites, and recompute global glueings without regenerating the entire semantic object from scratch.

**Why it helps minimal annotation.** This makes empirical evidence a serious substitute for hand-written contracts in many ordinary programs.

**Decidable-core strategy.** Trace incorporation can be formulated as set intersection on local sections, which keeps the dynamic step simple and soundly stratified.

**Implementation implication.** A future runtime companion could make this direction especially attractive for Torch-heavy workflows.

### Algorithm family 6: Global-section frontier extraction

**Main procedure.** Rather than enumerating frontiers of atom subsets, enumerate frontiers of global sections ordered by information, annotation cost, proof burden, and obstruction rank.

**Why it helps minimal annotation.** This yields suggestions like “one extra witness transport resolves three ambiguity classes” instead of “select two more atoms.”

**Decidable-core strategy.** The optimizer works over summaries of local glueings and obstruction classes, not arbitrary higher-order objects, preserving implementability.

**Implementation implication.** This is the place where the current MaxSMT frontier would be most radically reimagined.

### Algorithm family 7: Cover-aware benchmark and explanation rendering

**Main procedure.** Render local sections, overlaps, obstruction classes, and proof transports in a human-readable explanation layer that tells users how semantics were glued together.

**Why it helps minimal annotation.** Minimal annotation only feels trustworthy if users can see why the system recovered so much from so little input.

**Decidable-core strategy.** Rendering is proof- and solver-agnostic because it operates on the symbolic cover data structure.

**Implementation implication.** The existing explanation/diagnostic surfaces would become much richer and less clause-centric.

## Worked examples and benchmark implications

A convincing rewrite should force the benchmark suite to become more ambitious. The point is to make the system look less like a clever contract extractor and more like a proof-producing, information-maximizing semantic environment.

### Example 1: Sorting algorithm with wrapper-heavy dataflow

**Scenario.** A proof-oriented user provides a local invariant about partition correctness and permutation preservation, while ordinary helper functions wrap, rename, and partially apply the sorter before returning values to downstream consumers.

**What the new mathematics should infer automatically.** The system should glue local proof sections with dataflow sections so that wrapper-heavy ordinary code still inherits sortedness and permutation semantics without manual restatement.

**Where proofs enter.** Only the nontrivial transport and partition lemma should need explicit proof terms. Wrapper correctness should follow from descent.

**Why the current monograph would feel weaker here.** Today the monograph still reasons too much in terms of fact transport. The sheaf version would make wrapper transparency a structural theorem.

### Example 2: Torch ranking pipeline with nested views and slices

**Scenario.** A Tensor is sorted, then passed through nested view operations, then sliced and indexed through several helper layers that mix data and proof-free orchestration code.

**What the new mathematics should infer automatically.** Order, permutation, shape, and indexing information should glue across the corresponding Torch-generated sites, surviving aliasing and nested return expressions.

**Where proofs enter.** If a user supplies a proof that a helper preserves sort-derived semantics under a nontrivial transformation, that proof should register as a transport map and improve future inference globally.

**Why the current monograph would feel weaker here.** The current monograph can approximate this through theory packs, but the sheaf rewrite would make the cross-pack compatibility story central rather than incidental.

### Example 3: Graph search with dynamic trace guidance

**Scenario.** An ordinary Python implementation of BFS or Dijkstra is run on a few representative inputs, generating traces about queue monotonicity, visitation discipline, and path reconstruction structure.

**What the new mathematics should infer automatically.** Trace contraction should narrow the space of admissible local invariant sections enough that the tool can suggest only one or two human-supplied invariants, not a full proof script.

**Where proofs enter.** The proof-oriented surface would still be needed for the deepest global invariant, but much of the typing burden should vanish through local contraction and descent.

**Why the current monograph would feel weaker here.** This is exactly the kind of “regular programmer plus optional proof expert” workflow the current monograph gestures toward but does not yet formalize strongly.

### Example 4: Heap-sensitive protocol wrapper

**Scenario.** A program updates object fields, passes them through protocol wrappers, and then performs indexing or aggregation on collections of those objects.

**What the new mathematics should infer automatically.** Heap sites, protocol sites, and collection sites should interact through overlaps so that local field invariants become reusable in protocol conformance proofs and downstream refinements.

**Where proofs enter.** A human proof should only be needed when a wrapper changes ownership or invariant framing in a way not expressible by default transport.

**Why the current monograph would feel weaker here.** The current system has pieces of heap and protocol reasoning, but a sheaf semantics would unify them mathematically.

### Example 5: Recursive divide-and-conquer proof surface

**Scenario.** A user or LLM writes an explicit proof module for a divide-and-conquer algorithm with local lemmas on subproblems and a gluing lemma for recombination.

**What the new mathematics should infer automatically.** The checker should build proof sites for the recursive branches and combine them into a global correctness section for the algorithm and its wrappers.

**Where proofs enter.** Only the branch and gluing lemmas need to be explicit; all wrapper-level contracts should be inherited automatically.

**Why the current monograph would feel weaker here.** This proposal makes the proof surface feel like a native semantic calculus rather than an optional addon.

### Example 6: Mixed proof-first and no-annotation user workflow

**Scenario.** A proof-oriented team publishes a few transport lemmas for data structures or tensor operators, while downstream users write ordinary Python with almost no annotations.

**What the new mathematics should infer automatically.** The downstream users should receive stronger inferred types because the global section space has already been constrained by published transport maps and library covers.

**Where proofs enter.** This turns proof work into reusable infrastructure rather than one-off certificate writing.

**Why the current monograph would feel weaker here.** That is the strongest possible justification for combining proof-first and low-annotation workflows in one system.

## Chapter-by-chapter rewrite of the monograph

The current document is organized around optimization-backed signature packing. A genuinely radical replacement should alter the order of exposition, the primitive judgments, the role of examples, and the very notion of what counts as a proof obligation.

### Replacement chapter 1: From signatures to sites

Replace the opening definition of semantic signatures with a chapter that defines observation sites, covers, restriction maps, and local semantic sections. The key didactic change is that the reader first learns how information is distributed spatially across a program before learning how it is compressed into a user-facing contract.

**Mandatory new mathematical payload.** Formal category of sites, notion of cover, local semantic posets, and proof-boundary annotations on stalks.

**User-facing consequence.** Users see immediately why sparse observations and sparse annotations can still imply strong global structure.

### Replacement chapter 2: Descent instead of packing

The chapter currently devoted to optimization-backed packing should be replaced by a descent chapter explaining gluing conditions, compatibility maps, obstruction extraction, and extension sets.

**Mandatory new mathematical payload.** Descent lemmas, overlap constraints, and uniqueness criteria for global sections.

**User-facing consequence.** The system can explain inference failures structurally rather than as optimizer leftovers.

### Replacement chapter 3: Theory packs as geometry constructors

Rewrite the theory-pack chapter so packs create sites and overlaps, not merely atoms. Use Torch as the running example because it makes the cover intuition vivid.

**Mandatory new mathematical payload.** Formal interface for cover constructors and stalk logics.

**User-facing consequence.** Nested or aliased operations are no longer mysterious corner cases.

### Replacement chapter 4: Proof modules as transport layers

Expand the proof-surface chapter into a theory of transport maps, commuting squares, and reusable local proofs.

**Mandatory new mathematical payload.** Transport semantics and proof-boundary integration.

**User-facing consequence.** Proof-oriented users get leverage instead of paperwork.

### Replacement chapter 5: Dynamic refinement as contraction

Insert a major chapter explaining how traces refine sites and re-run descent without collapsing the distinction between proof and observation.

**Mandatory new mathematical payload.** Contraction operators, observational soundness, and empirical provenance.

**User-facing consequence.** Ordinary users can get stronger inference from execution, not only from syntax.

### Replacement chapter 6: Interprocedural functoriality

Promote wrapper transparency and interprocedural propagation from an implementation trick to a theorem-backed structural chapter.

**Mandatory new mathematical payload.** Pullback squares, reindexing, and functorial propagation of sections.

**User-facing consequence.** Users can trust that helper decomposition will not erase semantics arbitrarily.

### Replacement chapter 7: Obstruction-guided annotation synthesis

Replace the repair chapter with a mathematically sharper account of obstruction classes and ambiguity-resolving annotations.

**Mandatory new mathematical payload.** Basis of obstructions and minimal seeding theorem.

**User-facing consequence.** Annotation suggestions become more precise and less clause-centric.

### Replacement chapter 8: Torch and algorithm case studies as one story

Merge proof-heavy algorithm case studies and Torch refinement examples into one chapter on local-to-global semantics across domains.

**Mandatory new mathematical payload.** Common semantic site abstractions across ordinary Python, algorithms, and tensor code.

**User-facing consequence.** The system finally reads as one language, not multiple partially connected tools.

### Replacement chapter 9: Benchmark methodology

Revise the evaluation chapter so success is measured by obstruction rank reduction, annotation compression, and transport reuse—not only by number of inferred clauses.

**Mandatory new mathematical payload.** New metrics and empirical protocol.

**User-facing consequence.** Users understand what the tool is optimizing for and why that matches their effort.

### Replacement chapter 10: Foundations and future math

Close the monograph with a foundations chapter discussing when full cohomological language is necessary and when a combinatorial approximation suffices for implementation.

**Mandatory new mathematical payload.** Bridge between deep mathematics and an engineerable subset.

**User-facing consequence.** The project remains ambitious without becoming mystical.

## Research risks, but also why the direction is worth the cost

Each proposal here is intentionally more ambitious than a normal incremental design memo. That means each one carries substantial risk. The right question is not whether risk exists; it is whether the mathematical move buys a level of semantic compression and proof/program unification that the current framework cannot plausibly reach.

### Risk 1: Too much categorical machinery

**Problem.** Reviewers may worry that the mathematics is ornamental and not necessary for practical typing.

**Why the risk is acceptable.** The only acceptable answer is to show that the mathematics changes the annotation model: the user writes seeds that eliminate global ambiguity rather than manually enumerating clauses.

**Design mitigation.** Implement a combinatorial descent engine first, then present the topos/sheaf language as the clean semantic explanation of that engine.

### Risk 2: Obstruction theory may be too ambitious

**Problem.** Full cohomological machinery may exceed what is needed for the first implementation.

**Why the risk is acceptable.** That is acceptable as long as the monograph distinguishes the conceptual ideal from the implementable approximation.

**Design mitigation.** Start with overlap-conflict bases and only later generalize to richer invariants if the simpler version already demonstrates annotation compression.

### Risk 3: Site design could explode in complexity

**Problem.** A naive cover may create too many sites and too many overlaps to be practical.

**Why the risk is acceptable.** The cover is still the right abstraction because it exposes where complexity comes from instead of hiding it.

**Design mitigation.** Use sparse cover synthesis, summary sites, and pack-specific locality heuristics.

### Risk 4: Proof surface may become too academic

**Problem.** Proof-oriented features might feel detached from ordinary users.

**Why the risk is acceptable.** The opposite should happen if transport maps are reusable infrastructure for ordinary users.

**Design mitigation.** Require every proof-surface artifact to justify itself by improving low-annotation inference somewhere in the benchmark suite.

## Evaluation and success criteria


Success for this direction would be measured by whether the tool can explain inference as a global gluing phenomenon and whether annotation requests align with explicit ambiguity classes. The benchmark suite should report: number of sites, overlap density, obstruction rank before and after user input, degree of transport reuse across wrappers, and how many global semantics were recovered after only local seeding. On the proof side, the system should demonstrate that one local correctness lemma meaningfully improves downstream low-annotation typing. On the Torch side, it should show that nested, aliased, and interprocedural tensor code preserves semantic sections because of cover structure rather than ad hoc special cases.



If the monograph were rewritten around sheaf descent, the project would stop looking like “dependent typing with a clever optimizer” and start looking like a new semantics for information-rich programming environments. That would be a genuine mathematical departure. It would justify a much bigger claim: that minimal annotation is possible not because the system guesses well, but because the program, proof, and runtime observations together determine a global semantic object whose ambiguity can be measured and systematically removed.



## Addendum: automatic synthesis of input refinements for runtime-error avoidance

A major weakness of many refinement-typing proposals is that they explain how to enrich *results* while remaining vague about how to synthesize the *input-side* refinements needed to avoid runtime errors. A sheaf-descent rewrite can do much better. In this framework, a runtime error is not just a failed assertion; it is evidence that some local site admits no valid section under the observed input neighborhood. That suggests a direct mathematical response: derive the smallest refinement on the input sites whose restrictions make all downstream sites nonempty and glueable.

The key move is to introduce an **input-boundary sheaf** $\mathsf{In}$ paired with the main semantic presheaf. The objects of $\mathsf{In}$ are input neighborhoods: argument shape regions, value-order regimes, heap-state assumptions, alias exclusions, protocol preconditions, and index-range windows. Each runtime-error mode determines a bad open subfamily in the downstream sites. For example, an out-of-bounds indexing operation excludes all local sections whose input neighborhoods permit $i 
otin [0, n)$; a `view` failure excludes all neighborhoods whose shape product is inconsistent with the target; a divide-by-zero failure excludes any neighborhood allowing the denominator site to contain zero; a protocol failure excludes neighborhoods where a required method or field is absent. Runtime-error avoidance then becomes a *lift problem*: find an input section $
ho$ such that every downstream site reachable from the input restriction of $
ho$ admits at least one valid local section, and such that the resulting family glues globally.

This produces a radically stronger interpretation of “necessary refinements on inputs.” The goal is not to guess a large precondition and hope it suffices. The goal is to compute the **minimal boundary refinement** whose image under restriction and transport avoids the bad open family everywhere in the cover. Because the cover already records how information propagates through wrappers, library calls, traces, proofs, and interprocedural summaries, the same descent engine that glues output semantics can also push backward from failing or potentially failing sites to synthesize the weakest safe input neighborhood. The generated refinement is therefore not merely a static guard; it is a global explanation of which input ambiguity classes would otherwise make some local semantic site empty.

### Local-to-global construction of safe input refinements

The sheaf version should add an explicit backwards pass on the site cover. First, each local site exports a **viability predicate** on its incoming neighborhoods. For tensor-shape sites, viability states that the incoming dimensions admit the target reshape or broadcast. For indexing sites, viability states that the incoming index domain is included in the source domain. For algorithmic proof sites, viability states that the input region supports the invariant or decreases the ranking function. For heap/protocol sites, viability states that the incoming object neighborhood contains the required fields, alias exclusions, or ownership framing assumptions.

Second, these local viability predicates are transported backward along the morphisms of the site category. If a `torch.sort` site is always safe but a subsequent indexing site is not, the indexing viability condition is pulled back through the permutation/index overlap so that the input neighborhood reflects not only raw index bounds but also the semantics of how indices were produced. If a wrapper introduces aliases or a branch refines a value, the backward transport records that structure rather than discarding it. Third, the system computes a meet or greatest lower safe region over the input boundary sites. This meet is the synthesized input refinement. It is “minimal” in the lattice sense that any weaker input region would fail to guarantee nonempty local semantics somewhere downstream.

This is the point where the sheaf machinery becomes much more powerful than simple guard mining. Guard mining can collect `if x is not None`, `if len(xs) > 0`, or `if i < xs.shape[0]`. The sheaf system can explain *which global family of downstream sites* forced those conditions, which ones are redundant because they are implied by other local overlaps, and which additional higher-level refinement would collapse several downstream obligations at once. An ideal explanation would say: “to make all reachable tensor-shape, indexing, and proof sites nonempty, the weakest input section requires `rank(xs) >= 1`, `shape(xs, 0) > 0`, and `compatible_view(xs, -1)`.” That is already much closer to the dream system.

### Runtime-error avoidance as nonemptiness of semantic neighborhoods

A particularly attractive theorem schema emerges from this formulation. Let $E$ denote the family of sites that correspond to runtime-error modes or operations with partial semantics. Then define a safe input section $
ho$ to be one such that for every site $U$ reachable from the input boundary under the program’s semantic morphisms, the restricted local section set is nonempty:

$$orall U \in E.\; \mathsf{Sem}(U \mid 
ho) 
eq arnothing.$$

The runtime-error synthesis theorem should then say that if $
ho_\min$ is the greatest lower bound of all safe input sections and local soundness plus descent soundness hold, then any execution starting in $
ho_\min$ is protected from the represented runtime-error family. More interestingly, the theorem should also characterize when the safe input refinement is *strictly smaller* than the conjunction of all local guard predicates because some guards are redundant after gluing. That is exactly the sort of mathematical leverage the current monograph does not yet have.

### How this changes the user story

For ordinary users, the system should now be able to synthesize preconditions and input contracts even when the user never wrote them. Those preconditions are justified by the same global semantics that support output contracts, not by a separate ad hoc guard extractor. For proof-oriented users, proofs can make input synthesis better by proving transport lemmas or showing that certain local error sites are unreachable under an invariant. This is extremely important for algorithms. Many algorithmic correctness proofs contain hidden preconditions—nonempty arrays, admissible graph weights, permutation-domain constraints, or ownership assumptions. In the sheaf rewrite, those become explicit synthesized input sections, not buried assumptions.

For Torch code, this addendum is essential. The system should not only infer that a function returns a sorted tensor or a reshaped view; it should also synthesize the weakest input refinement ensuring that `sort`, `view`, `slice`, `gather`, or `index_select` never hit a runtime error region. That means constraints like nonzero dimensions, compatible reshape cardinalities, valid index ranges, and device or dtype compatibility should be represented as input-boundary sections. A future benchmark chapter should absolutely include “safe input refinement synthesis” as a headline metric.

### New chapter and theorem implications

If this addendum were folded into a full rewrite, the monograph would need one more dedicated chapter: **Backward Descent and Safe Input Refinement Synthesis**. That chapter would formalize partial operators as sites with bad open families, define the backward transport of viability predicates, and prove that the synthesized input section is minimal among all safe refinements in the chosen lattice of admissible input neighborhoods. It would also need concrete case studies: empty-list avoidance, divide-by-zero prevention, tensor-view safety, index safety, and proof-assisted algorithm precondition synthesis.

In short, a sheaf-descent rewrite does not merely explain how to infer more output semantics from fewer annotations. It also explains how to synthesize the smallest globally justified input refinements needed to exclude runtime-error neighborhoods. That strengthens the proposal substantially, because it shows that “maximum information” includes not only richer postconditions but also automatically recovered preconditions that make programs safer to run.


## Supplement: bidirectional synthesis of input and output refinements

The strongest version of the sheaf-descent proposal should not separate safe input synthesis from rich output typing. The same cover should support a **bidirectional refinement problem**: compute the weakest boundary section on inputs that keeps every partial operator semantically viable, and then compute the strongest globally glued output section forced by that safe boundary together with the available local evidence. In other words, the system should synthesize a pair $(\rho_{in}, \rho_{out})$ where $\rho_{in}$ is a minimal safe input refinement and $\rho_{out}$ is a maximal informative output refinement compatible with descent.

This is a much better story than treating preconditions and postconditions as unrelated artifacts. In the sheaf setting they are adjoint views of the same global semantic object. Backward transport along the cover computes the admissible input neighborhoods needed to avoid runtime-error sites. Forward descent from those neighborhoods computes the richest result section, witness family, and relational output constraints that remain globally glueable. The system can then say not only “these are the inputs under which execution is safe,” but also “under exactly those weakest safe inputs, these are the strongest output refinements now justified.”

Mathematically, the rewrite should introduce a **safe-boundary-to-output extension operator**. Given a synthesized safe input boundary section $\rho_{in}$, define

$$\mathrm{Out}(\rho_{in}) = \max \{\sigma_{out} \mid \exists \sigma \text{ global section with } \sigma|_{\partial_{in}} = \rho_{in} \text{ and } \sigma|_{\partial_{out}} = \sigma_{out} \}.$$

The optimization problem is therefore not merely to avoid failure, but to solve

$$\min \; \mathrm{cost}(\rho_{in}) - \lambda \cdot \mathrm{info}(\mathrm{Out}(\rho_{in}))$$

subject to the nonemptiness and descent constraints. This captures exactly the user-facing dream: ask for or synthesize the weakest input assumptions that still unlock the strongest possible result specification.

### Fixed-point computation

Algorithmically, the dream implementation should alternate two passes until stabilization. A backward viability pass computes which input neighborhoods keep every error-sensitive site nonempty. A forward descent pass computes which output facts, witnesses, sortedness relations, shape equalities, alias facts, and theorem-indexed guarantees are forced once those safe neighborhoods are assumed. If forward descent reveals a stronger output fact that itself implies additional structure on overlaps, the backward pass can sharpen or simplify the required inputs by eliminating redundant boundary assumptions. The result is a bidirectional fixed point: minimal safe input, maximal justified output.

This fixed-point story is especially attractive for Torch code. A synthesized input refinement such as shape compatibility or index-domain validity should immediately strengthen output refinements like exact result shape, sortedness, or value/index coupling. Conversely, some strong output transport laws may reveal that weaker input constraints suffice than naive guard conjunction would suggest. The cover structure makes that interaction principled.

### Why this matters for the monograph rewrite

With this supplement, the sheaf direction can claim a much more ambitious theorem program: local evidence plus sparse annotations determine a globally glued *contract transformer* from inputs to outputs. That is stronger than a type checker and stronger than a postcondition extractor. It is a mathematically unified account of how to synthesize safe preconditions and rich postconditions together under one descent discipline.
