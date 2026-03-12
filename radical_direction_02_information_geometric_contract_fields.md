# Direction II — Information-Geometric Contract Fields: Rate–Distortion Optimal Dependent Typing

## Executive thesis


This direction rewrites the monograph so that a type is no longer best understood as a set of predicates, nor even as a global section of a sheaf, but as a point or distribution on a semantic manifold. The core claim is radical: minimal annotation should be analyzed as a low-rate coding problem, and maximum-information typing should be analyzed as a rate–distortion or mutual-information optimization problem over a field of latent dependent contracts. Instead of asking which clauses to select, the system asks how much semantic information about a value can be recovered from syntax, dynamic observations, library priors, and optional proofs under a fixed annotation-rate budget.

In that view, proof-first users and ordinary users occupy different regions of the same geometric object. A proof resolves uncertainty, turning a diffuse posterior over contracts into a sharp stratum. A dynamic refinement trace supplies noisy measurements that update the posterior. A minimal annotation is not just a cheaper contract; it is a short codeword that drives the posterior into a small, high-information region. The payoff is conceptual unification: correctness proofs, dynamic refinement typing, LLM-provided hints, and ordinary inference all become information channels into one contract field.


## Why this would require a complete rewrite of `dependent_typing_as_optimization.tex`


The current monograph treats optimization as selection over candidates. The information-geometric rewrite says that this is still too discrete and too syntactic. The object we really want is a semantic random field over latent dependent contracts. Candidate atoms are merely coordinates or observables on that field. Annotation cost is communication cost. Incorrect or weakly informative typing corresponds to high posterior entropy or high distortion. The entire story of minimal annotation, theory growth, and proof integration becomes cleaner if we say explicitly that the goal is to infer the sharpest posterior contract field subject to bounded symbolic communication and bounded trusted proof effort.



The slogan “minimal annotation, maximum information” becomes a theorem schema from information theory. Minimal annotation means minimizing the code length of human- or LLM-supplied semantic messages. Maximum information means maximizing mutual information between those messages plus machine-extracted evidence and the latent semantic contract. The dream system would not ask users for clauses because clauses are easy to print; it would ask for the bit of information that most sharply contracts the posterior geometry.


## Signature mathematical kernel


Let $Z_e$ be a latent dependent contract variable for expression $e$, ranging over a semialgebraic or proof-indexed contract manifold $\mathcal{M}_e$. Let $O_e$ denote observations extracted from syntax, traces, theory packs, wrappers, and proof artifacts. The typing problem is to compute a posterior

$$p(Z_e \mid O_e, A_e) \propto p(O_e \mid Z_e) \, p(A_e \mid Z_e) \, p(Z_e),$$

where $A_e$ is the user/LLM annotation channel. Minimal annotation is the constrained optimization

$$\max_{A : \mathbb{E}[\ell(A)] \le B} I(Z ; O, A) - \lambda D(Z, \widehat{Z}),$$

where $\ell(A)$ is code length and $D$ is a semantic distortion functional derived from proof obligations, violated refinements, or incompleteness penalties. Proofs are modeled as posterior-collapse operators onto low-entropy submanifolds, while dynamic traces provide partial observations that change the posterior without eliminating provenance distinctions.


## Foundational primitives

The current monograph still thinks in terms of selected facts. This rewrite says that facts are only visible coordinates of a richer information-bearing contract field. That shift changes optimization, explanation, proof reuse, and dynamic refinement all at once.

### Primitive 1: Semantic random fields over dependent contracts

**Core move.** Every relevant expression carries a latent semantic contract variable rather than a single inferred signature. The system tracks uncertainty explicitly, because uncertainty is exactly what minimal annotation is supposed to reduce.

**Formal object.** The latent space should include carrier types, refinement coordinates, witness coordinates, algorithmic-correctness coordinates, and provenance/trust coordinates. Different program regions can be coupled through a graphical model or field structure.

**Minimal-annotation consequence.** A short annotation is powerful only if it drastically reduces posterior entropy. This model lets the system measure that directly instead of guessing from clause counts.

**Algorithmic and library consequence.** Torch evidence, proof artifacts, and ordinary syntax become different observation channels feeding one posterior object.

**Why this is more radical than the current monograph.** The current monograph optimizes over explicit candidates. The geometric rewrite says candidates are merely projections of a richer latent object.

### Primitive 2: Contract manifolds and charts

**Core move.** Instead of a flat universe of propositions, organize semantic possibilities into a manifold or stratified space with interpretable coordinates: order, shape, aliasing, witness existence, loop ranking, protocol conformance, and so on.

**Formal object.** Different decidable fragments become charts on the manifold. Local inference operates within charts, while global optimization moves between charts via transport maps or natural-gradient updates.

**Minimal-annotation consequence.** Minimal annotation means asking for the coordinate with the highest information gain per bit, not the first residual clause the solver failed on.

**Algorithmic and library consequence.** A proof can pin an exact chart or stratum. A dynamic trace can shrink uncertainty within a chart. Theory packs can propose coordinate families instead of only atoms.

**Why this is more radical than the current monograph.** The current document distinguishes theory packs and proof boundaries, but it still lacks a geometric state space in which those distinctions are native.

### Primitive 3: Annotation as a rate-limited communication channel

**Core move.** Human or LLM annotations should be treated as coded semantic messages with a budget. This makes minimal annotation a communication problem, not just a stylistic preference.

**Formal object.** The channel can assign costs to syntax length, proof complexity, trust burden, or even cognitive complexity. The optimizer then chooses queries or annotation suggestions that maximize posterior contraction per unit cost.

**Minimal-annotation consequence.** This gives an exact mathematical meaning to “ask for the smallest thing that matters.”

**Algorithmic and library consequence.** For ordinary Torch users the tool can prefer a one-line exemplar or a single `ensures` clause if that carries high information. For proof users it can ask for the one missing lemma that sharply contracts uncertainty.

**Why this is more radical than the current monograph.** The present monograph has annotation costs, but not a full information-channel semantics.

### Primitive 4: Posterior contraction as typing success

**Core move.** Typing should be judged by how sharply the posterior concentrates around semantically strong contracts, not only by whether a solver can prove a handful of propositions.

**Formal object.** Success metrics include entropy, posterior volume, chart diameter, and distortion to an ideal proof-complete contract. Different user surfaces correspond to different ways of driving contraction.

**Minimal-annotation consequence.** A tiny annotation that cuts posterior volume by orders of magnitude is better than many longer annotations that merely add redundant clauses.

**Algorithmic and library consequence.** The tool can surface uncertainty maps, not just yes/no residuals, giving users more meaningful interaction when full automation is impossible.

**Why this is more radical than the current monograph.** The current monograph has frontiers of packed signatures. Here the frontier lives in information space.

### Primitive 5: Fisher–Rao or natural geometry on contracts

**Core move.** If contract states live in a manifold-like object, then inference should respect its geometry rather than using arbitrary coordinate-wise heuristics.

**Formal object.** The monograph could define a Fisher-like metric or an information geometry induced by observation likelihoods and trust penalties. This would justify natural-gradient style updates and explain why some annotations are globally informative while others are merely local tweaks.

**Minimal-annotation consequence.** Minimal annotation is then geodesic steering: use the shortest high-information message to move the posterior into the desired semantic basin.

**Algorithmic and library consequence.** Optimization becomes more principled and potentially more sample-efficient when using dynamic evidence or LLM hints.

**Why this is more radical than the current monograph.** This is radically more ambitious than the current weighted selection viewpoint.

### Primitive 6: Optimal transport between proof-first and ordinary surfaces

**Core move.** Proof-heavy user inputs and low-annotation ordinary programs should not merely feed the same backend; they should be connected by a transport problem on semantic distributions.

**Formal object.** A proof can be viewed as an almost degenerate posterior, while an unannotated program starts diffuse. The system should learn or compute transports that push ordinary evidence toward proof-quality semantics when library or algorithm structure supports it.

**Minimal-annotation consequence.** This means a proof-first library author can make low-annotation usage better by publishing transports, not only by publishing signatures.

**Algorithmic and library consequence.** Torch helper libraries, algorithm libraries, or theorem bundles become information-shaping priors over downstream code.

**Why this is more radical than the current monograph.** The current monograph speaks of shared semantic core; transport would make that statement mathematically concrete.

### Primitive 7: Semantic distortion functionals

**Core move.** Not all typing mistakes are equal. The system should quantify how far an inferred contract is from the ideal one using a distortion function tailored to semantics, not just clause mismatch.

**Formal object.** Distortion may weight proof incompleteness, wrong carrier type, missing witness, wrong shape relation, wrong permutation semantics, or inability to verify an algorithmic postcondition. This turns type quality into a continuous optimization target.

**Minimal-annotation consequence.** The best user prompt is the one that most decreases distortion per bit of annotation.

**Algorithmic and library consequence.** This directly supports prioritization: a tiny annotation that fixes a catastrophic semantic ambiguity beats a longer annotation that only refines cosmetic facts.

**Why this is more radical than the current monograph.** The current monograph uses scores and costs but not a full distortion-theoretic semantics.

### Primitive 8: Proofs as posterior-collapse operators

**Core move.** A proof is valuable because it rules out almost all nearby semantic worlds. Treating proofs as entropy-collapse operators gives a unified account of formal verification and type inference.

**Formal object.** A checked proof term or certified transport map updates the contract field by projecting onto a verified stratum. The remaining uncertainty is then only observational or modeling uncertainty, not logical doubt.

**Minimal-annotation consequence.** This provides a graceful path from zero-annotation use to proof-first use: the user adds proof material only when they want sharper contraction than observation alone can support.

**Algorithmic and library consequence.** Algorithmic proofs and Torch refinement typing truly inhabit one mathematical object rather than sitting in different layers with weak bridges.

**Why this is more radical than the current monograph.** The current monograph already respects proof boundaries, but this rewrite gives proofs an information-theoretic role rather than only a logical one.

### Primitive 9: Dynamic evidence assimilation

**Core move.** Runtime traces, assertions, test outcomes, and sampled tensor shapes become observation variables that update the contract field without pretending to be formal proofs.

**Formal object.** Each dynamic observation contributes a likelihood factor. The system can keep provenance explicit by tagging which posterior contraction came from proof, from syntax, from library priors, or from data.

**Minimal-annotation consequence.** This is ideal for ordinary users: running a representative program can give the analyzer a rich observation packet before any manual contract writing happens.

**Algorithmic and library consequence.** Torch programs become a first-class beneficiary because dynamic evidence is cheap and semantically informative.

**Why this is more radical than the current monograph.** The current monograph is compatible with evidence, but this rewrite would put evidence assimilation at the center.

### Primitive 10: Chart-wise decidable kernels

**Core move.** The dream system can still stay sane by insisting that every chart or coordinate family has a certified projection into a decidable kernel fragment or a clearly marked residual channel.

**Formal object.** This yields a hybrid of rich probabilistic or geometric state plus exact local verification. The manifold is ambitious; the kernel slices remain disciplined.

**Minimal-annotation consequence.** Users therefore get powerful inference without silent trust inflation.

**Algorithmic and library consequence.** It becomes realistic to add new semantic families while keeping the trusted core explicit.

**Why this is more radical than the current monograph.** The current monograph stratifies proof boundaries; the geometric version would stratify charts and update operators as well.

## How proofs of algorithmic correctness and refinement typing would coexist


In this rewrite, algorithmic correctness proofs are not special because they mention induction or invariants. They are special because they collapse uncertainty much more aggressively than ordinary observations. A proof should therefore be modeled as a low-entropy operator on the contract manifold: it projects the posterior onto a thin stratum where certain correctness coordinates are fixed exactly. This gives a principled account of why a small proof can unlock large downstream inference gains. One proof about a sorting helper does not just add `sorted(result)`; it changes the posterior geometry for every consumer that depends on the helper’s latent contract field.

This perspective also changes how proof obligations should be rendered. Instead of showing a list of residual goals, the system could report which semantic coordinates remain high-entropy and which proof artifact would most reduce the posterior volume. That is a much stronger story for interactive proof assistance and for LLM-produced semantic hints.



Dynamic refinement typing for Torch becomes especially natural here. Tensor programs generate enormous amounts of low-cost observational information: ranks, dimensions, aliasing relations, monotonicity surrogates, shape equalities, and control-dependent value flows. These observations should be treated as noisy measurements of a latent contract field. A `torch.sort` call creates a posterior over order/permutation/index semantics; a `view` operation induces a transport on shape coordinates; an indexing operation observes relations between a result and a source tensor. The system’s job is to fuse these observations and decide whether the posterior is already sharp enough to act as a practical dependent type or whether one short user message would contract it further.


## Theorem agenda

A rewrite of this kind needs theorems that justify the information story, not just examples that happen to look good. The theorem list below is chosen so that the resulting monograph could make strong claims about why sparse human communication is enough.

### Theorem target 1: Posterior consistency under valid proofs

**Statement shape.** Show that when a proof artifact is valid, posterior mass outside the proved semantic stratum converges to zero under the proof-update operator.

**Why it matters.** This formalizes why proof-first inputs should dominate ordinary observations when both exist.

**Likely proof strategy.** Combine kernel soundness with a measure-theoretic or order-theoretic update rule that respects trust classification.

### Theorem target 2: Rate–distortion annotation bound

**Statement shape.** Derive lower and upper bounds on the expected annotation rate required to achieve a target semantic distortion level on a benchmark family.

**Why it matters.** This is the cleanest theoretical expression of the monograph’s slogan.

**Likely proof strategy.** Use an application-specific distortion functional and show how theory priors and dynamic evidence reduce the rate needed to hit the same distortion target.

### Theorem target 3: Mutual-information optimal query theorem

**Statement shape.** Prove that under suitable conditional-independence assumptions, the best user query is the one maximizing expected mutual information with the latent contract field per unit annotation cost.

**Why it matters.** This would justify active annotation suggestions mathematically.

**Likely proof strategy.** Standard information-gain arguments adapted to a structured contract manifold and costed channel model.

### Theorem target 4: Frontier equivalence theorem

**Statement shape.** Relate the current packed-signature frontiers to level sets or projections of the richer information-geometric objective, showing when the old optimizer is a coarse approximation to the new one.

**Why it matters.** This gives a migration path from current infrastructure to the radical rewrite.

**Likely proof strategy.** Show that under a discrete chart and degenerate posterior family, frontier packing is recovered as a special case.

### Theorem target 5: Monotone theory-addition theorem

**Statement shape.** Show that adding a sound theory pack cannot increase Bayes risk or semantic distortion, though it may leave them unchanged.

**Why it matters.** This turns open-world theory growth into a rigorous monotonicity claim.

**Likely proof strategy.** Treat new theory packs as prior refinements or new observation families and prove risk monotonicity under soundness assumptions.

### Theorem target 6: Proof/trace provenance decomposition

**Statement shape.** Prove that posterior contraction can be decomposed into trace-induced, syntax-induced, library-induced, and proof-induced contributions under the selected factorization.

**Why it matters.** This supports explanation and trust auditing.

**Likely proof strategy.** Use factorized likelihoods and KL-divergence decomposition.

### Theorem target 7: Chart conservativity theorem

**Statement shape.** Show that projections to decidable chart kernels are conservative with respect to certain observable contract coordinates.

**Why it matters.** This keeps the radical math compatible with a practical implementation.

**Likely proof strategy.** A commuting-diagram argument between rich semantic updates and chart projections.

### Theorem target 8: Transport stability theorem

**Statement shape.** Establish that proof-first library contracts improve downstream ordinary-user posterior concentration whenever the transport map is certified and the downstream code lies in the transport basin.

**Why it matters.** This theorem captures the dream of shared proof infrastructure for low-annotation users.

**Likely proof strategy.** Define a transport basin and show posterior contraction after pushforward or pullback along the certified map.

## Algorithmic realization

The geometry is only worth keeping if it produces concrete algorithmic gains. Each algorithm family below is phrased as a bridge from rich latent semantics to a practical, partially decidable implementation.

### Algorithm family 1: Variational contract-field inference

**Main procedure.** Approximate the posterior over latent contracts using structured variational families whose coordinates correspond to carriers, predicates, witnesses, proof status, and theory activation.

**Why it helps minimal annotation.** The system can estimate which user bit would most reduce posterior entropy before asking for anything.

**Decidable-core strategy.** Local chart projections give exact checks for the fragments we trust, while variational inference handles richer uncertainty outside those slices.

**Implementation implication.** This would likely become the new centerpiece around which current frontier, repair, and renderer layers are reorganized.

### Algorithm family 2: Natural-gradient annotation planning

**Main procedure.** Use the geometry of the contract manifold to choose annotation prompts or proof requests that move the posterior in the steepest high-value direction under the metric.

**Why it helps minimal annotation.** This is a direct operationalization of “small message, large information gain.”

**Decidable-core strategy.** Gradient steps are only used to rank proposals; all accepted updates are still projected into checked local fragments.

**Implementation implication.** The current repair loop could be generalized into an active-information planner.

### Algorithm family 3: Rate-aware proof synthesis

**Main procedure.** Treat proof search as a compression problem: search for the shortest proof artifact whose checked consequence contracts the most important uncertainty region.

**Why it helps minimal annotation.** This avoids overlong proof scripts and aligns proof effort with actual semantic information gain.

**Decidable-core strategy.** Candidate proofs are still checked by the existing kernel or bounded solver bridge.

**Implementation implication.** Proof surface tooling would need scoring by posterior contraction rather than only by satisfiable obligations.

### Algorithm family 4: Dynamic evidence fusion for Torch

**Main procedure.** Fuse symbolic Torch theory priors with runtime shape/index observations, amortized operator statistics, and optional user assertions into one posterior update.

**Why it helps minimal annotation.** Many users will never need to write more than a couple of semantic hints if the evidence fusion layer is strong enough.

**Decidable-core strategy.** Only stable, chart-projectable dynamic summaries should affect the trusted contract slice.

**Implementation implication.** This would turn the current static theory packs into hybrid static and dynamic semantic channels.

### Algorithm family 5: Optimal-transport contract transfer

**Main procedure.** Learn or compute transports from proof-rich source contracts to low-annotation target code patterns so that verified libraries become semantic priors for ordinary code.

**Why it helps minimal annotation.** Published proofs then reduce future annotation burden automatically.

**Decidable-core strategy.** Transport outputs must still land in chart-wise verifiable families before being trusted.

**Implementation implication.** This could be especially strong for standard algorithm and tensor libraries.

### Algorithm family 6: Distortion-calibrated frontier extraction

**Main procedure.** Instead of ranking frontiers only by score and cost, rank them by semantic distortion, posterior entropy, and the marginal value of extra annotation.

**Why it helps minimal annotation.** Users see choices like “cheap but semantically blurry” versus “one extra line yields a sharp contract.”

**Decidable-core strategy.** The frontier remains a finite presentation even if the latent object is richer.

**Implementation implication.** The renderer layer would become much more informative and honest about uncertainty.

### Algorithm family 7: Posterior provenance rendering

**Main procedure.** Show which pieces of the contract field were determined by proof, by theory packs, by traces, and by user hints, including their relative information contributions.

**Why it helps minimal annotation.** This makes the minimal-annotation claim auditable instead of mysterious.

**Decidable-core strategy.** Rendering operates over the factorized posterior summary and checked chart projections.

**Implementation implication.** This would make the explanation subsystem significantly more novel.

## Worked examples and benchmark implications

A convincing rewrite should force the benchmark suite to become more ambitious about uncertainty, proof leverage, and dynamic evidence. The examples below illustrate the kinds of stories this framework could tell far better than the existing discrete packing view.

### Example 1: Low-annotation sorting correctness

**Scenario.** A user writes an ordinary sorting pipeline with wrappers and only one short semantic hint, while a proof author provides a library proof of permutation preservation.

**What the new mathematics should infer automatically.** The contract field should combine the proof prior with observed wrapper behavior to contract onto sortedness and permutation semantics automatically.

**Where proofs enter.** Only the library proof needs explicit certification; ordinary users benefit through posterior transport.

**Why the current monograph would feel weaker here.** The current monograph can imitate this with explicit atoms, but not with the same information-theoretic clarity.

### Example 2: Torch training-step refinement

**Scenario.** A training loop manipulates batches, logits, losses, and index tensors while only sparse runtime evidence is available from representative runs.

**What the new mathematics should infer automatically.** Dynamic observations should sharply contract the posterior over shape, broadcasting, and index-safety coordinates without requiring long annotations.

**Where proofs enter.** If a proof module establishes invariants about a custom layer, that proof should contract the relevant coordinates for all downstream code.

**Why the current monograph would feel weaker here.** This would make dynamic refinement typing much more principled than ad hoc post-hoc checking.

### Example 3: Graph algorithm with optional proof hints

**Scenario.** An ordinary Python graph algorithm is partially guided by a few LLM-suggested invariants but otherwise mostly unannotated.

**What the new mathematics should infer automatically.** The system should score those hints by expected information gain and retain only the ones that meaningfully reduce distortion.

**Where proofs enter.** Formal proofs enter when the user wants sharp contraction on the deepest correctness coordinate.

**Why the current monograph would feel weaker here.** The rewrite could explain why some hints are redundant and some are decisive.

### Example 4: Proof-rich library, low-annotation client

**Scenario.** A proof-oriented team publishes correctness facts and transport operators for a library, while client code is largely unannotated.

**What the new mathematics should infer automatically.** Client posteriors should start already concentrated because the prior is informative and certified.

**Where proofs enter.** The client writes no proof; the library proof acts as a compressed semantic source.

**Why the current monograph would feel weaker here.** This is the cleanest manifestation of shared infrastructure across user classes.

### Example 5: Alias-heavy tensor orchestration

**Scenario.** A tensor program uses many local aliases, nested views, slices, and helper wrappers.

**What the new mathematics should infer automatically.** The posterior should retain sort, shape, and indexing semantics because the underlying information geometry is tied to latent contracts rather than syntax alone.

**Where proofs enter.** Only truly nonlocal semantic transitions need explicit proof or annotation.

**Why the current monograph would feel weaker here.** The current implementation is moving in this direction, but the geometric rewrite would make it foundational.

### Example 6: Interactive annotation planning session

**Scenario.** A user asks the system what single annotation would most improve confidence in a downstream property.

**What the new mathematics should infer automatically.** The answer should be chosen by expected KL reduction or distortion drop, not by a heuristic rank of predicates.

**Where proofs enter.** If the best move is a proof lemma rather than a surface contract, the system should say so explicitly.

**Why the current monograph would feel weaker here.** This would transform the UX into an information-planning tool rather than a passive checker.

## Chapter-by-chapter rewrite of the monograph

The present text would need more than added sections. It would need a new order of explanation, new primary objects, and a new style of evaluation.

### Replacement chapter 1: Latent contract fields instead of semantic signatures

The monograph should open by defining latent contract variables, posterior objects, chart projections, and distortion rather than immediately presenting signatures as the canonical semantic unit.

**Mandatory new mathematical payload.** Probability or measure semantics over contracts, chart structure, and provenance factorization.

**User-facing consequence.** Readers immediately see why annotations are treated as information, not just syntax.

### Replacement chapter 2: Observation channels

Add a major chapter on syntax, proofs, traces, and library theories as distinct observation channels into the contract field.

**Mandatory new mathematical payload.** Likelihood factors, prior structure, and provenance decomposition.

**User-facing consequence.** Users understand how ordinary code, traces, and proofs cooperate.

### Replacement chapter 3: Rate-limited annotation semantics

Replace simple annotation-cost discussion with a formal coding model and rate budget.

**Mandatory new mathematical payload.** Code length models and active query objective.

**User-facing consequence.** Annotation suggestions feel principled rather than arbitrary.

### Replacement chapter 4: Geometric optimization core

The optimization chapter becomes a rate–distortion and posterior-contraction chapter with variational approximations and frontier projections.

**Mandatory new mathematical payload.** Mutual information, distortion, entropy, and geometric update rules.

**User-facing consequence.** Users can see why one additional hint is more valuable than another.

### Replacement chapter 5: Proof collapse operators

The proof chapter should explain how checked proofs contract posterior mass and why that is different from ordinary evidence.

**Mandatory new mathematical payload.** Projection operators and trust-aware update laws.

**User-facing consequence.** Proof-first users get mathematically privileged leverage without bypassing trust boundaries.

### Replacement chapter 6: Torch as a hybrid static/dynamic case study

Rewrite the Torch sections so they explicitly illustrate fusion of library priors and dynamic evidence.

**Mandatory new mathematical payload.** Posterior update examples for sort, shape, and indexing coordinates.

**User-facing consequence.** Torch users see a clear path from runs to stronger types.

### Replacement chapter 7: Algorithm proofs as information compressors

Frame algorithmic correctness proofs as compressed messages with extreme semantic impact rather than only as theorem scripts.

**Mandatory new mathematical payload.** Proof length versus posterior contraction discussions.

**User-facing consequence.** Proof effort becomes economically interpretable.

### Replacement chapter 8: Renderer redesign

Update explanation chapters to report uncertainty, distortion, and information gain along with recovered contracts.

**Mandatory new mathematical payload.** Posterior summaries and provenance attribution.

**User-facing consequence.** Users get an honest and useful picture of what the tool knows.

### Replacement chapter 9: Benchmark methodology

Evaluate by distortion reduction, entropy contraction, and annotation rate rather than only by proof-goal discharge.

**Mandatory new mathematical payload.** Information-centric empirical metrics.

**User-facing consequence.** Performance claims become much more convincing.

### Replacement chapter 10: Foundational synthesis

Conclude with a chapter connecting this view to Bayesian program analysis, information geometry, proof theory, and compression-based semantics.

**Mandatory new mathematical payload.** A broad but coherent mathematical synthesis.

**User-facing consequence.** The project reads like a new theory, not a collection of features.

## Research risks, but also why the direction is worth the cost

The value of a radical rewrite is that it can explain the system’s behavior at a deeper level than a growing pile of heuristics. The cost is that the mathematics has to earn its place.

### Risk 1: Probabilistic semantics may look too soft

**Problem.** Some readers may fear that an information-geometric story weakens the crispness of dependent typing.

**Why the risk is acceptable.** The opposite should happen if the rewrite is disciplined: rich uncertainty is kept in the latent field, while trusted conclusions are projected into exact chart kernels.

**Design mitigation.** Keep the trusted kernel explicit and use probabilistic structure only to guide which exact facts are worth certifying or querying.

### Risk 2: Modeling choices could dominate behavior

**Problem.** Bad priors or distortion choices might lead to poor annotation suggestions.

**Why the risk is acceptable.** That is a real risk, but it is also honest: any minimal-annotation system is already making hidden choices about value and uncertainty.

**Design mitigation.** Expose priors, distortion components, and provenance in the renderer and benchmark them openly.

### Risk 3: Geometry may be hard to justify formally

**Problem.** A metric or manifold metaphor can become decorative if not tied to algorithms and proofs.

**Why the risk is acceptable.** That only means the rewrite must state precise update rules and prove frontier equivalence results.

**Design mitigation.** Require every geometric notion to correspond to an actual optimization or explanation primitive.

### Risk 4: Too much dependence on dynamic evidence

**Problem.** Torch users may worry that the system becomes overly empirical.

**Why the risk is acceptable.** The design explicitly separates evidence provenance, so empirical contraction never masquerades as proof.

**Design mitigation.** Present dynamic evidence as an optional amplifier, not a replacement for proof or symbolic inference.

## Evaluation and success criteria


This direction succeeds if the monograph can make information-theoretic claims that are genuinely operational: one short annotation or one short proof should measurably shrink semantic distortion, and the system should be able to explain why. Benchmarks should record entropy before and after theory packs, proofs, traces, and user hints; the cost in bits or structured-message complexity of each user intervention; and the distortion remaining on important correctness coordinates. A great result would show that proof-rich libraries dramatically reduce annotation rate for ordinary clients, and that dynamic Torch evidence contracts the posterior enough that many scripts need almost no manual refinement text.



The information-geometric rewrite would make the monograph feel radically more modern and more ambitious. It would explain, in the strongest available mathematical language, why a system can ask users for very little yet still recover contracts with far more semantic content than ordinary refinement typing. Instead of treating this as a lucky property of heuristics, it would present it as a consequence of contract inference as compression, communication, and posterior contraction.


## Extended appendix 1: posterior geometry, diagnostics, and migration notes

The appendix below intentionally restates the main proposal in an even more implementation-aware language so the eventual LaTeX rewrite can spread the ideas across theorem sections, case studies, and UX chapters.

### Appendix primitive note 1.1: Semantic random fields over dependent contracts under implementation pressure

A likely engineering objection is that semantic random fields over dependent contracts sounds elegant but difficult to fit into a usable tool. The answer is that the rich object is not introduced for aesthetic reasons. Every relevant expression carries a latent semantic contract variable rather than a single inferred signature. The system tracks uncertainty explicitly, because uncertainty is exactly what minimal annotation is supposed to reduce. The latent space should include carrier types, refinement coordinates, witness coordinates, algorithmic-correctness coordinates, and provenance/trust coordinates. Different program regions can be coupled through a graphical model or field structure. The real minimal-annotation payoff is that the system can quantify how much uncertainty remains and which small user message would contract it most sharply. A short annotation is powerful only if it drastically reduces posterior entropy. This model lets the system measure that directly instead of guessing from clause counts. In practice this means proof-rich users and ordinary users no longer need two conceptually different pipelines; they are simply providing different kinds of information to the same latent field.

### Appendix primitive note 1.2: Contract manifolds and charts under implementation pressure

A likely engineering objection is that contract manifolds and charts sounds elegant but difficult to fit into a usable tool. The answer is that the rich object is not introduced for aesthetic reasons. Instead of a flat universe of propositions, organize semantic possibilities into a manifold or stratified space with interpretable coordinates: order, shape, aliasing, witness existence, loop ranking, protocol conformance, and so on. Different decidable fragments become charts on the manifold. Local inference operates within charts, while global optimization moves between charts via transport maps or natural-gradient updates. The real minimal-annotation payoff is that the system can quantify how much uncertainty remains and which small user message would contract it most sharply. Minimal annotation means asking for the coordinate with the highest information gain per bit, not the first residual clause the solver failed on. In practice this means proof-rich users and ordinary users no longer need two conceptually different pipelines; they are simply providing different kinds of information to the same latent field.

### Appendix primitive note 1.3: Annotation as a rate-limited communication channel under implementation pressure

A likely engineering objection is that annotation as a rate-limited communication channel sounds elegant but difficult to fit into a usable tool. The answer is that the rich object is not introduced for aesthetic reasons. Human or LLM annotations should be treated as coded semantic messages with a budget. This makes minimal annotation a communication problem, not just a stylistic preference. The channel can assign costs to syntax length, proof complexity, trust burden, or even cognitive complexity. The optimizer then chooses queries or annotation suggestions that maximize posterior contraction per unit cost. The real minimal-annotation payoff is that the system can quantify how much uncertainty remains and which small user message would contract it most sharply. This gives an exact mathematical meaning to “ask for the smallest thing that matters.” In practice this means proof-rich users and ordinary users no longer need two conceptually different pipelines; they are simply providing different kinds of information to the same latent field.

### Appendix primitive note 1.4: Posterior contraction as typing success under implementation pressure

A likely engineering objection is that posterior contraction as typing success sounds elegant but difficult to fit into a usable tool. The answer is that the rich object is not introduced for aesthetic reasons. Typing should be judged by how sharply the posterior concentrates around semantically strong contracts, not only by whether a solver can prove a handful of propositions. Success metrics include entropy, posterior volume, chart diameter, and distortion to an ideal proof-complete contract. Different user surfaces correspond to different ways of driving contraction. The real minimal-annotation payoff is that the system can quantify how much uncertainty remains and which small user message would contract it most sharply. A tiny annotation that cuts posterior volume by orders of magnitude is better than many longer annotations that merely add redundant clauses. In practice this means proof-rich users and ordinary users no longer need two conceptually different pipelines; they are simply providing different kinds of information to the same latent field.

### Appendix primitive note 1.5: Fisher–Rao or natural geometry on contracts under implementation pressure

A likely engineering objection is that fisher–rao or natural geometry on contracts sounds elegant but difficult to fit into a usable tool. The answer is that the rich object is not introduced for aesthetic reasons. If contract states live in a manifold-like object, then inference should respect its geometry rather than using arbitrary coordinate-wise heuristics. The monograph could define a Fisher-like metric or an information geometry induced by observation likelihoods and trust penalties. This would justify natural-gradient style updates and explain why some annotations are globally informative while others are merely local tweaks. The real minimal-annotation payoff is that the system can quantify how much uncertainty remains and which small user message would contract it most sharply. Minimal annotation is then geodesic steering: use the shortest high-information message to move the posterior into the desired semantic basin. In practice this means proof-rich users and ordinary users no longer need two conceptually different pipelines; they are simply providing different kinds of information to the same latent field.

### Appendix primitive note 1.6: Optimal transport between proof-first and ordinary surfaces under implementation pressure

A likely engineering objection is that optimal transport between proof-first and ordinary surfaces sounds elegant but difficult to fit into a usable tool. The answer is that the rich object is not introduced for aesthetic reasons. Proof-heavy user inputs and low-annotation ordinary programs should not merely feed the same backend; they should be connected by a transport problem on semantic distributions. A proof can be viewed as an almost degenerate posterior, while an unannotated program starts diffuse. The system should learn or compute transports that push ordinary evidence toward proof-quality semantics when library or algorithm structure supports it. The real minimal-annotation payoff is that the system can quantify how much uncertainty remains and which small user message would contract it most sharply. This means a proof-first library author can make low-annotation usage better by publishing transports, not only by publishing signatures. In practice this means proof-rich users and ordinary users no longer need two conceptually different pipelines; they are simply providing different kinds of information to the same latent field.

### Appendix primitive note 1.7: Semantic distortion functionals under implementation pressure

A likely engineering objection is that semantic distortion functionals sounds elegant but difficult to fit into a usable tool. The answer is that the rich object is not introduced for aesthetic reasons. Not all typing mistakes are equal. The system should quantify how far an inferred contract is from the ideal one using a distortion function tailored to semantics, not just clause mismatch. Distortion may weight proof incompleteness, wrong carrier type, missing witness, wrong shape relation, wrong permutation semantics, or inability to verify an algorithmic postcondition. This turns type quality into a continuous optimization target. The real minimal-annotation payoff is that the system can quantify how much uncertainty remains and which small user message would contract it most sharply. The best user prompt is the one that most decreases distortion per bit of annotation. In practice this means proof-rich users and ordinary users no longer need two conceptually different pipelines; they are simply providing different kinds of information to the same latent field.

### Appendix primitive note 1.8: Proofs as posterior-collapse operators under implementation pressure

A likely engineering objection is that proofs as posterior-collapse operators sounds elegant but difficult to fit into a usable tool. The answer is that the rich object is not introduced for aesthetic reasons. A proof is valuable because it rules out almost all nearby semantic worlds. Treating proofs as entropy-collapse operators gives a unified account of formal verification and type inference. A checked proof term or certified transport map updates the contract field by projecting onto a verified stratum. The remaining uncertainty is then only observational or modeling uncertainty, not logical doubt. The real minimal-annotation payoff is that the system can quantify how much uncertainty remains and which small user message would contract it most sharply. This provides a graceful path from zero-annotation use to proof-first use: the user adds proof material only when they want sharper contraction than observation alone can support. In practice this means proof-rich users and ordinary users no longer need two conceptually different pipelines; they are simply providing different kinds of information to the same latent field.

### Appendix primitive note 1.9: Dynamic evidence assimilation under implementation pressure

A likely engineering objection is that dynamic evidence assimilation sounds elegant but difficult to fit into a usable tool. The answer is that the rich object is not introduced for aesthetic reasons. Runtime traces, assertions, test outcomes, and sampled tensor shapes become observation variables that update the contract field without pretending to be formal proofs. Each dynamic observation contributes a likelihood factor. The system can keep provenance explicit by tagging which posterior contraction came from proof, from syntax, from library priors, or from data. The real minimal-annotation payoff is that the system can quantify how much uncertainty remains and which small user message would contract it most sharply. This is ideal for ordinary users: running a representative program can give the analyzer a rich observation packet before any manual contract writing happens. In practice this means proof-rich users and ordinary users no longer need two conceptually different pipelines; they are simply providing different kinds of information to the same latent field.

### Appendix primitive note 1.10: Chart-wise decidable kernels under implementation pressure

A likely engineering objection is that chart-wise decidable kernels sounds elegant but difficult to fit into a usable tool. The answer is that the rich object is not introduced for aesthetic reasons. The dream system can still stay sane by insisting that every chart or coordinate family has a certified projection into a decidable kernel fragment or a clearly marked residual channel. This yields a hybrid of rich probabilistic or geometric state plus exact local verification. The manifold is ambitious; the kernel slices remain disciplined. The real minimal-annotation payoff is that the system can quantify how much uncertainty remains and which small user message would contract it most sharply. Users therefore get powerful inference without silent trust inflation. In practice this means proof-rich users and ordinary users no longer need two conceptually different pipelines; they are simply providing different kinds of information to the same latent field.

### Appendix algorithm note 1.1: Variational contract-field inference as a systems contribution

If one wanted a paper-worthy implementation story, variational contract-field inference would be one of the core differentiators. Approximate the posterior over latent contracts using structured variational families whose coordinates correspond to carriers, predicates, witnesses, proof status, and theory activation. It matters that the method continues to respect a chart-wise trusted core. Local chart projections give exact checks for the fragments we trust, while variational inference handles richer uncertainty outside those slices. The best possible engineering result would be a tool that openly reports uncertainty while still projecting stable, high-value facts into precise user-facing contracts. This would likely become the new centerpiece around which current frontier, repair, and renderer layers are reorganized.

### Appendix algorithm note 1.2: Natural-gradient annotation planning as a systems contribution

If one wanted a paper-worthy implementation story, natural-gradient annotation planning would be one of the core differentiators. Use the geometry of the contract manifold to choose annotation prompts or proof requests that move the posterior in the steepest high-value direction under the metric. It matters that the method continues to respect a chart-wise trusted core. Gradient steps are only used to rank proposals; all accepted updates are still projected into checked local fragments. The best possible engineering result would be a tool that openly reports uncertainty while still projecting stable, high-value facts into precise user-facing contracts. The current repair loop could be generalized into an active-information planner.

### Appendix algorithm note 1.3: Rate-aware proof synthesis as a systems contribution

If one wanted a paper-worthy implementation story, rate-aware proof synthesis would be one of the core differentiators. Treat proof search as a compression problem: search for the shortest proof artifact whose checked consequence contracts the most important uncertainty region. It matters that the method continues to respect a chart-wise trusted core. Candidate proofs are still checked by the existing kernel or bounded solver bridge. The best possible engineering result would be a tool that openly reports uncertainty while still projecting stable, high-value facts into precise user-facing contracts. Proof surface tooling would need scoring by posterior contraction rather than only by satisfiable obligations.

### Appendix algorithm note 1.4: Dynamic evidence fusion for Torch as a systems contribution

If one wanted a paper-worthy implementation story, dynamic evidence fusion for torch would be one of the core differentiators. Fuse symbolic Torch theory priors with runtime shape/index observations, amortized operator statistics, and optional user assertions into one posterior update. It matters that the method continues to respect a chart-wise trusted core. Only stable, chart-projectable dynamic summaries should affect the trusted contract slice. The best possible engineering result would be a tool that openly reports uncertainty while still projecting stable, high-value facts into precise user-facing contracts. This would turn the current static theory packs into hybrid static and dynamic semantic channels.

### Appendix algorithm note 1.5: Optimal-transport contract transfer as a systems contribution

If one wanted a paper-worthy implementation story, optimal-transport contract transfer would be one of the core differentiators. Learn or compute transports from proof-rich source contracts to low-annotation target code patterns so that verified libraries become semantic priors for ordinary code. It matters that the method continues to respect a chart-wise trusted core. Transport outputs must still land in chart-wise verifiable families before being trusted. The best possible engineering result would be a tool that openly reports uncertainty while still projecting stable, high-value facts into precise user-facing contracts. This could be especially strong for standard algorithm and tensor libraries.

### Appendix algorithm note 1.6: Distortion-calibrated frontier extraction as a systems contribution

If one wanted a paper-worthy implementation story, distortion-calibrated frontier extraction would be one of the core differentiators. Instead of ranking frontiers only by score and cost, rank them by semantic distortion, posterior entropy, and the marginal value of extra annotation. It matters that the method continues to respect a chart-wise trusted core. The frontier remains a finite presentation even if the latent object is richer. The best possible engineering result would be a tool that openly reports uncertainty while still projecting stable, high-value facts into precise user-facing contracts. The renderer layer would become much more informative and honest about uncertainty.

### Appendix algorithm note 1.7: Posterior provenance rendering as a systems contribution

If one wanted a paper-worthy implementation story, posterior provenance rendering would be one of the core differentiators. Show which pieces of the contract field were determined by proof, by theory packs, by traces, and by user hints, including their relative information contributions. It matters that the method continues to respect a chart-wise trusted core. Rendering operates over the factorized posterior summary and checked chart projections. The best possible engineering result would be a tool that openly reports uncertainty while still projecting stable, high-value facts into precise user-facing contracts. This would make the explanation subsystem significantly more novel.

### Appendix theorem note 1.1: why Posterior consistency under valid proofs changes the claim language

Show that when a proof artifact is valid, posterior mass outside the proved semantic stratum converges to zero under the proof-update operator. This formalizes why proof-first inputs should dominate ordinary observations when both exist. Combine kernel soundness with a measure-theoretic or order-theoretic update rule that respects trust classification. Without theorems of this form, the phrase 'minimal annotation, maximum information' remains rhetoric. With them, the monograph can honestly claim that it studies semantic compression rather than only ad hoc automation.

### Appendix theorem note 1.2: why Rate–distortion annotation bound changes the claim language

Derive lower and upper bounds on the expected annotation rate required to achieve a target semantic distortion level on a benchmark family. This is the cleanest theoretical expression of the monograph’s slogan. Use an application-specific distortion functional and show how theory priors and dynamic evidence reduce the rate needed to hit the same distortion target. Without theorems of this form, the phrase 'minimal annotation, maximum information' remains rhetoric. With them, the monograph can honestly claim that it studies semantic compression rather than only ad hoc automation.

### Appendix theorem note 1.3: why Mutual-information optimal query theorem changes the claim language

Prove that under suitable conditional-independence assumptions, the best user query is the one maximizing expected mutual information with the latent contract field per unit annotation cost. This would justify active annotation suggestions mathematically. Standard information-gain arguments adapted to a structured contract manifold and costed channel model. Without theorems of this form, the phrase 'minimal annotation, maximum information' remains rhetoric. With them, the monograph can honestly claim that it studies semantic compression rather than only ad hoc automation.

### Appendix theorem note 1.4: why Frontier equivalence theorem changes the claim language

Relate the current packed-signature frontiers to level sets or projections of the richer information-geometric objective, showing when the old optimizer is a coarse approximation to the new one. This gives a migration path from current infrastructure to the radical rewrite. Show that under a discrete chart and degenerate posterior family, frontier packing is recovered as a special case. Without theorems of this form, the phrase 'minimal annotation, maximum information' remains rhetoric. With them, the monograph can honestly claim that it studies semantic compression rather than only ad hoc automation.

### Appendix theorem note 1.5: why Monotone theory-addition theorem changes the claim language

Show that adding a sound theory pack cannot increase Bayes risk or semantic distortion, though it may leave them unchanged. This turns open-world theory growth into a rigorous monotonicity claim. Treat new theory packs as prior refinements or new observation families and prove risk monotonicity under soundness assumptions. Without theorems of this form, the phrase 'minimal annotation, maximum information' remains rhetoric. With them, the monograph can honestly claim that it studies semantic compression rather than only ad hoc automation.

### Appendix theorem note 1.6: why Proof/trace provenance decomposition changes the claim language

Prove that posterior contraction can be decomposed into trace-induced, syntax-induced, library-induced, and proof-induced contributions under the selected factorization. This supports explanation and trust auditing. Use factorized likelihoods and KL-divergence decomposition. Without theorems of this form, the phrase 'minimal annotation, maximum information' remains rhetoric. With them, the monograph can honestly claim that it studies semantic compression rather than only ad hoc automation.

### Appendix theorem note 1.7: why Chart conservativity theorem changes the claim language

Show that projections to decidable chart kernels are conservative with respect to certain observable contract coordinates. This keeps the radical math compatible with a practical implementation. A commuting-diagram argument between rich semantic updates and chart projections. Without theorems of this form, the phrase 'minimal annotation, maximum information' remains rhetoric. With them, the monograph can honestly claim that it studies semantic compression rather than only ad hoc automation.

### Appendix theorem note 1.8: why Transport stability theorem changes the claim language

Establish that proof-first library contracts improve downstream ordinary-user posterior concentration whenever the transport map is certified and the downstream code lies in the transport basin. This theorem captures the dream of shared proof infrastructure for low-annotation users. Define a transport basin and show posterior contraction after pushforward or pullback along the certified map. Without theorems of this form, the phrase 'minimal annotation, maximum information' remains rhetoric. With them, the monograph can honestly claim that it studies semantic compression rather than only ad hoc automation.


## Addendum: automatic synthesis of input refinements for runtime-error avoidance

A serious information-geometric rewrite cannot stop at saying “posterior uncertainty contracts around rich output contracts.” If the system is to earn the label *minimum annotation, maximum information*, it must also automatically synthesize the input refinements needed to keep execution away from runtime-error regions. In the geometric language, runtime-error avoidance means shaping the admissible input distribution so that posterior mass over failure-inducing executions becomes negligible or exactly zero in the trusted chart projection.

The right mathematical move is to define an **input contract field** $X$ and a **runtime-failure field** $F$. Here $X$ ranges over possible refinements on arguments, heap assumptions, index domains, shape constraints, ownership side conditions, and protocol requirements, while $F$ ranges over error events such as out-of-bounds access, invalid reshape, zero division, null dereference, unsupported protocol dispatch, aliasing violations, or impossible witness obligations. The system then solves a bilevel inference problem: infer the posterior over semantic contracts *and* infer the weakest input-side refinement that drives the failure probability below a target threshold, or to zero after projection into the exact chart.

One clean objective is

$$\min_{R \in \mathcal{R}_{	ext{inputs}}} \; \mathbb{E}[\ell(R)] + \lambda \, \mathbb{P}(F \mid O, R) + \mu D(\widehat{Z}_R, Z^*),$$

where $R$ is an input refinement code, $\ell(R)$ is its description length, $\mathbb{P}(F \mid O, R)$ is residual runtime-failure risk after incorporating observations $O$ and refinement $R$, and $D(\widehat{Z}_R, Z^*)$ is distortion to the ideal semantic contract. In plain language: synthesize the smallest input message whose downstream effect is to collapse most or all runtime-failure probability while preserving a high-information contract posterior. This is exactly the input-side dual of the original slogan.

### Safe-input synthesis as posterior shaping

The current monograph’s optimization logic becomes far more powerful once we distinguish between *contract contraction* and *failure-mass contraction*. A candidate refinement on inputs should not be ranked only by whether it appears in guards or by whether it helps prove a postcondition. It should also be ranked by how strongly it suppresses the posterior mass assigned to failure trajectories. For example:

- for indexing code, the refinement `0 <= i < len(xs)` contracts the posterior over out-of-bounds states;
- for shape-sensitive Torch code, the refinement `prod(shape(xs)) = prod(target_shape)` or `shape(xs,0) > 0` contracts the posterior over invalid reshape or empty-dimension failures;
- for algorithmic correctness proofs, a refinement such as “all weights are nonnegative” contracts the posterior over losing executions of Dijkstra-like routines and simultaneously contracts the semantic uncertainty about the algorithm’s correctness coordinates;
- for heap/protocol code, a refinement like `implements(ReadAt)` or `owns(self.buf)` contracts failure risk and proof burden at once.

This makes automatic input refinement synthesis a principled information-planning problem. The tool should ask: what short refinement code eliminates the most posterior failure mass per unit annotation cost? That is much more nuanced than simply extracting every guard and returning them as `requires` clauses.

### Geometric interpretation of weakest safe refinements

The strongest version of this idea is that safe inputs form a **safe submanifold** or **safe feasible region** of the input contract space. Runtime failures define forbidden strata: hypersurfaces or semialgebraic bad regions where shape relations break, denominators vanish, indices escape bounds, protocols are violated, or invariants fail. The synthesis problem is to project the current diffuse input posterior onto the smallest nearby region that avoids the forbidden strata while still supporting a high-information output contract.

This suggests two complementary algorithms. The first is variational: optimize a compact symbolic refinement code whose posterior pushforward reduces failure risk. The second is exact: on decidable charts, compute weakest safe predicates by solving a symbolic viability problem. In practice the dream implementation would combine them. Rich probabilistic geometry would suggest candidate refinements; the trusted chart projection would certify the strongest exact slice of those refinements that is mechanically justified.

This is where the proposal becomes extremely attractive for Torch programs. Many runtime errors in tensor code are shape, index, device, dtype, or broadcasting mismatches. These are not merely Boolean mistakes; they are geometric constraints on admissible inputs. A rate–distortion rewrite can give those constraints a precise role: they are the shortest symbolic codes that move the posterior from a high-risk region into a safe and semantically informative region. An ideal renderer could then say: “the highest-value refinement is `shape(xs,0) > 0` because it removes 82% of the failure mass and simultaneously resolves uncertainty about the legality of the subsequent slice.”

### Interaction with proof-first users

A proof-rich workflow also improves input refinement synthesis. Proofs can impose exact support conditions on the posterior. A verified transport lemma or algorithmic theorem may imply that certain inputs are inadmissible or that some risky regimes are semantically irrelevant. This is important for algorithm verification because many correctness theorems hide side conditions like sorted inputs, acyclic graphs, monotone priorities, or alias exclusions. In the information-geometric rewrite, those are no longer second-class assumptions. They become structured input refinements whose information value can be measured and whose downstream contraction effect can be reused.

A library proof should therefore act like a prior-shaping or support-restricting artifact. For downstream users, this means the system can often synthesize stronger input requirements with almost no local annotation, because the proof-induced prior already tells the posterior which input regions are even meaningful. This is a powerful answer to the user-experience question: proof authors do not merely certify outputs; they make safe input synthesis easier for everyone else.

### New theorem program for input-side safety

A refined monograph should add at least three theorem targets here. First, a **safe-support theorem** stating that under sound chart projection, any synthesized refinement with zero projected failure mass excludes the represented runtime-error family. Second, a **minimum-rate safe refinement theorem** showing that the selected input code is optimal or near-optimal under the chosen rate–risk objective. Third, a **proof-assisted support contraction theorem** showing that certified proofs can reduce the minimum annotation rate needed to achieve the same failure-risk target.

These theorems would substantially strengthen the proposal, because they would show that minimal annotation is not only about recovering richer meanings after the fact; it is also about synthesizing the smallest useful preconditions that keep the program inside the safe region in the first place.

### Monograph consequences

This addendum deserves an explicit new chapter in any future rewrite: **Input-Side Contract Compression and Runtime-Risk Suppression**. That chapter should develop the geometry of safe input regions, distinguish symbolic and probabilistic notions of safety, present algorithms for synthesizing weakest safe refinements on decidable charts, and show how proofs and traces reduce the cost of safe refinement. Benchmarks should then report not only recovered postconditions but also failure-mass reduction and synthesized input requirements.

In short, an information-geometric rewrite becomes much more compelling once it can say: the same mathematics that compresses rich postconditions from sparse hints also synthesizes the smallest high-value input refinements needed to avoid runtime errors. That makes the direction feel far less like an abstract reinterpretation and far more like a blueprint for a genuinely stronger system.


## Supplement: bidirectional synthesis of input and output refinements

The information-geometric direction becomes substantially stronger once it treats preconditions and postconditions as two coupled compression problems on one semantic channel. The system should not only synthesize the shortest input-side refinement code that suppresses runtime-failure probability; it should also synthesize the shortest or most informative output-side refinement code that describes what the safe execution region guarantees afterward. This yields a **bidirectional rate–distortion program** over input and output contract fields.

Let $R_{in}$ range over symbolic refinements on the admissible input region and let $R_{out}$ range over symbolic refinements summarizing the output contract. The dream objective is something like

$$\max_{R_{in}, R_{out}} I(Z_{out}; O, R_{in}, R_{out}) - \lambda \ell(R_{in}) - \mu \ell(R_{out}) - \eta \mathbb{P}(F \mid O, R_{in}),$$

where $Z_{out}$ is the latent output contract, $F$ is runtime failure, and the information terms are evaluated after projecting onto a trusted decidable chart. In words: choose the smallest total refinement message whose input part makes execution safe and whose output part captures as much guaranteed semantic information as possible.

This is a beautiful way to reinterpret “output refinements.” They are not arbitrary pretty annotations. They are compressed codes for the posterior-safe guarantees that remain after the input hedge has restricted the admissible executions. A good output refinement should therefore be chosen by *information yield*: which output coordinate family communicates the most about the posterior-safe semantic manifold per unit description length? That could mean sortedness, exact shape, permutation relations, witness existence, ownership transfer, or algorithm-specific correctness coordinates.

### Safe posterior, rich posterior

The geometry should therefore distinguish two contraction phases. First, input refinement synthesis projects the posterior away from dangerous regions that carry runtime-failure mass. Second, output refinement synthesis compresses the resulting safe posterior into a compact semantic message. The two phases are coupled. Better input refinements often make sharper output refinements possible, while sharper output coordinates can make certain input constraints provably redundant because the posterior already rules out dangerous regions.

This suggests a practical architecture. Use probabilistic or variational machinery to propose candidate input and output refinements jointly. Then, on decidable charts, certify the exact symbolic slice of that proposal: the weakest safe input predicate and the strongest chart-certified output predicate family. For ordinary users, the tool could render both automatically as synthesized `requires` and `ensures`-style contracts. For proof-oriented users, the same machinery could generate sharper theorem statements by making explicit which output guarantees become available once the inferred safe support condition is assumed.

### Why this matters for runtime safety

This supplement addresses a crucial usability gap. Users do not only want to know how to avoid failure; they want to know what they *get* in exchange for satisfying the synthesized input refinement. A rate–distortion rewrite can now answer: satisfying this short input refinement moves execution into a safe posterior basin, and within that basin the strongest low-rate output summary is, for example, exact reshape legality plus output shape equalities, sortedness of the value tensor, and permutation-index coupling. That is far more actionable than a bare precondition or a long undifferentiated proof report.

With this addition, the information-geometric monograph could claim to synthesize **minimal safe inputs and maximal compressed outputs** under one unified information objective. That makes the direction feel much closer to a dream implementation rather than only a philosophical reframing.
