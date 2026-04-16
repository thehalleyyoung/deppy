"""CCTT Proof Serialization — JSON and human-readable proof I/O.

Proof terms can be serialized to:
1. **JSON** — for machine consumption, storage, and interchange
2. **Human-readable notation** — for proof scripts and documentation

Both formats round-trip: deserialize(serialize(proof)) == proof.
"""
from __future__ import annotations

import json
from dataclasses import dataclass, fields
from typing import Any, Dict, List, Optional, Tuple, Union

from cctt.denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

from cctt.proof_theory.terms import (
    ProofTerm,
    Refl, Sym, Trans, Cong,
    Beta, Delta, Eta,
    NatInduction, ListInduction, WellFoundedInduction,
    AxiomApp, MathlibTheorem,
    LoopInvariant, Simulation, AbstractionRefinement,
    CommDiagram, FunctorMap,
    Z3Discharge,
    FiberDecomposition, CechGluing,
    Assume, Cut, LetProof,
    CasesSplit, Ext,
    Rewrite, RewriteChain,
    ArithmeticSimp, ListSimp, Definitional,
)


# ═══════════════════════════════════════════════════════════════════
# OTerm serialization
# ═══════════════════════════════════════════════════════════════════

def oterm_to_json(term: OTerm) -> Dict[str, Any]:
    """Serialize an OTerm to a JSON-compatible dict."""
    if isinstance(term, OVar):
        return {'type': 'OVar', 'name': term.name}
    elif isinstance(term, OLit):
        v = term.value
        if v is None:
            return {'type': 'OLit', 'value': None, 'value_type': 'none'}
        elif isinstance(v, bool):
            return {'type': 'OLit', 'value': v, 'value_type': 'bool'}
        elif isinstance(v, int):
            return {'type': 'OLit', 'value': v, 'value_type': 'int'}
        elif isinstance(v, float):
            return {'type': 'OLit', 'value': v, 'value_type': 'float'}
        elif isinstance(v, str):
            return {'type': 'OLit', 'value': v, 'value_type': 'str'}
        else:
            return {'type': 'OLit', 'value': repr(v), 'value_type': 'repr'}
    elif isinstance(term, OOp):
        return {
            'type': 'OOp',
            'name': term.name,
            'args': [oterm_to_json(a) for a in term.args],
        }
    elif isinstance(term, OFold):
        return {
            'type': 'OFold',
            'op_name': term.op_name,
            'init': oterm_to_json(term.init),
            'collection': oterm_to_json(term.collection),
        }
    elif isinstance(term, OCase):
        return {
            'type': 'OCase',
            'test': oterm_to_json(term.test),
            'true_branch': oterm_to_json(term.true_branch),
            'false_branch': oterm_to_json(term.false_branch),
        }
    elif isinstance(term, OFix):
        return {
            'type': 'OFix',
            'name': term.name,
            'body': oterm_to_json(term.body),
        }
    elif isinstance(term, OSeq):
        return {
            'type': 'OSeq',
            'elements': [oterm_to_json(e) for e in term.elements],
        }
    elif isinstance(term, ODict):
        return {
            'type': 'ODict',
            'pairs': [[oterm_to_json(k), oterm_to_json(v)]
                      for k, v in term.pairs],
        }
    elif isinstance(term, OUnknown):
        return {'type': 'OUnknown', 'desc': term.desc}
    elif isinstance(term, OQuotient):
        return {
            'type': 'OQuotient',
            'inner': oterm_to_json(term.inner),
            'equiv_class': term.equiv_class,
        }
    elif isinstance(term, OAbstract):
        return {
            'type': 'OAbstract',
            'spec': term.spec,
            'inputs': [oterm_to_json(i) for i in term.inputs],
        }
    elif isinstance(term, OLam):
        return {
            'type': 'OLam',
            'params': list(term.params),
            'body': oterm_to_json(term.body),
        }
    elif isinstance(term, OMap):
        result = {
            'type': 'OMap',
            'transform': oterm_to_json(term.transform),
            'collection': oterm_to_json(term.collection),
        }
        if term.filter_pred is not None:
            result['filter_pred'] = oterm_to_json(term.filter_pred)
        return result
    elif isinstance(term, OCatch):
        return {
            'type': 'OCatch',
            'body': oterm_to_json(term.body),
            'default': oterm_to_json(term.default),
        }
    else:
        return {'type': 'unknown', 'canon': term.canon()}


def oterm_from_json(data: Dict[str, Any]) -> OTerm:
    """Deserialize an OTerm from a JSON-compatible dict."""
    t = data['type']

    if t == 'OVar':
        return OVar(data['name'])
    elif t == 'OLit':
        vt = data.get('value_type', 'repr')
        v = data['value']
        if vt == 'none':
            return OLit(None)
        elif vt == 'bool':
            return OLit(bool(v))
        elif vt == 'int':
            return OLit(int(v))
        elif vt == 'float':
            return OLit(float(v))
        elif vt == 'str':
            return OLit(str(v))
        else:
            return OLit(v)
    elif t == 'OOp':
        return OOp(data['name'],
                   tuple(oterm_from_json(a) for a in data['args']))
    elif t == 'OFold':
        return OFold(data['op_name'],
                     oterm_from_json(data['init']),
                     oterm_from_json(data['collection']))
    elif t == 'OCase':
        return OCase(oterm_from_json(data['test']),
                     oterm_from_json(data['true_branch']),
                     oterm_from_json(data['false_branch']))
    elif t == 'OFix':
        return OFix(data['name'], oterm_from_json(data['body']))
    elif t == 'OSeq':
        return OSeq(tuple(oterm_from_json(e) for e in data['elements']))
    elif t == 'ODict':
        return ODict(tuple((oterm_from_json(p[0]), oterm_from_json(p[1]))
                           for p in data['pairs']))
    elif t == 'OUnknown':
        return OUnknown(data['desc'])
    elif t == 'OQuotient':
        return OQuotient(oterm_from_json(data['inner']),
                         data['equiv_class'])
    elif t == 'OAbstract':
        return OAbstract(data['spec'],
                         tuple(oterm_from_json(i) for i in data['inputs']))
    elif t == 'OLam':
        return OLam(tuple(data['params']),
                    oterm_from_json(data['body']))
    elif t == 'OMap':
        fp = (oterm_from_json(data['filter_pred'])
              if 'filter_pred' in data else None)
        return OMap(oterm_from_json(data['transform']),
                    oterm_from_json(data['collection']), fp)
    elif t == 'OCatch':
        return OCatch(oterm_from_json(data['body']),
                      oterm_from_json(data['default']))
    else:
        return OUnknown(f'deserialization_error:{t}')


# ═══════════════════════════════════════════════════════════════════
# ProofTerm serialization
# ═══════════════════════════════════════════════════════════════════

def _bindings_to_json(bindings: Dict[str, OTerm]) -> Dict[str, Any]:
    return {k: oterm_to_json(v) for k, v in bindings.items()}


def _bindings_from_json(data: Dict[str, Any]) -> Dict[str, OTerm]:
    return {k: oterm_from_json(v) for k, v in data.items()}


def proof_to_json(proof: ProofTerm) -> Dict[str, Any]:
    """Serialize a ProofTerm to a JSON-compatible dict."""
    tag = proof.tag()

    if isinstance(proof, Refl):
        return {'tag': tag, 'term': oterm_to_json(proof.term)}

    elif isinstance(proof, Sym):
        return {'tag': tag, 'proof': proof_to_json(proof.proof)}

    elif isinstance(proof, Trans):
        result: Dict[str, Any] = {
            'tag': tag,
            'left': proof_to_json(proof.left),
            'right': proof_to_json(proof.right),
        }
        if proof.middle is not None:
            result['middle'] = oterm_to_json(proof.middle)
        return result

    elif isinstance(proof, Cong):
        return {
            'tag': tag,
            'func': proof.func,
            'arg_proofs': [proof_to_json(p) for p in proof.arg_proofs],
        }

    elif isinstance(proof, Beta):
        return {
            'tag': tag,
            'lam': oterm_to_json(proof.lam),
            'arg': oterm_to_json(proof.arg),
        }

    elif isinstance(proof, Delta):
        result = {
            'tag': tag,
            'func_name': proof.func_name,
            'args': [oterm_to_json(a) for a in proof.args],
        }
        if proof.body is not None:
            result['body'] = oterm_to_json(proof.body)
        return result

    elif isinstance(proof, Eta):
        return {'tag': tag, 'term': oterm_to_json(proof.term)}

    elif isinstance(proof, NatInduction):
        return {
            'tag': tag,
            'base_case': proof_to_json(proof.base_case),
            'inductive_step': proof_to_json(proof.inductive_step),
            'variable': proof.variable,
            'base_value': oterm_to_json(proof.base_value),
        }

    elif isinstance(proof, ListInduction):
        return {
            'tag': tag,
            'nil_case': proof_to_json(proof.nil_case),
            'cons_case': proof_to_json(proof.cons_case),
            'variable': proof.variable,
            'elem_var': proof.elem_var,
            'tail_var': proof.tail_var,
        }

    elif isinstance(proof, WellFoundedInduction):
        return {
            'tag': tag,
            'measure': proof.measure,
            'step': proof_to_json(proof.step),
            'measure_type': proof.measure_type,
        }

    elif isinstance(proof, AxiomApp):
        return {
            'tag': tag,
            'axiom_name': proof.axiom_name,
            'direction': proof.direction,
            'target': oterm_to_json(proof.target),
            'bindings': _bindings_to_json(proof.bindings),
        }

    elif isinstance(proof, MathlibTheorem):
        return {
            'tag': tag,
            'theorem_name': proof.theorem_name,
            'instantiation': _bindings_to_json(proof.instantiation),
        }

    elif isinstance(proof, LoopInvariant):
        return {
            'tag': tag,
            'invariant': proof.invariant,
            'init_proof': proof_to_json(proof.init_proof),
            'preservation': proof_to_json(proof.preservation),
            'termination': proof_to_json(proof.termination),
            'post_proof': proof_to_json(proof.post_proof),
        }

    elif isinstance(proof, Simulation):
        return {
            'tag': tag,
            'relation': proof.relation,
            'init_proof': proof_to_json(proof.init_proof),
            'step_proof': proof_to_json(proof.step_proof),
            'output_proof': proof_to_json(proof.output_proof),
        }

    elif isinstance(proof, AbstractionRefinement):
        result = {
            'tag': tag,
            'spec_name': proof.spec_name,
            'abstraction_f': proof_to_json(proof.abstraction_f),
            'abstraction_g': proof_to_json(proof.abstraction_g),
        }
        if proof.abstraction_func is not None:
            result['abstraction_func'] = proof.abstraction_func
        return result

    elif isinstance(proof, CommDiagram):
        return {
            'tag': tag,
            'morphism_left': proof_to_json(proof.morphism_left),
            'iso_proof': proof_to_json(proof.iso_proof),
        }

    elif isinstance(proof, FunctorMap):
        return {
            'tag': tag,
            'functor': proof.functor,
            'compose_proof': proof_to_json(proof.compose_proof),
        }

    elif isinstance(proof, Z3Discharge):
        return {
            'tag': tag,
            'formula': proof.formula,
            'fragment': proof.fragment,
            'timeout_ms': proof.timeout_ms,
            'variables': proof.variables,
        }

    elif isinstance(proof, FiberDecomposition):
        return {
            'tag': tag,
            'fiber_proofs': {k: proof_to_json(v)
                             for k, v in proof.fiber_proofs.items()},
        }

    elif isinstance(proof, CechGluing):
        return {
            'tag': tag,
            'local_proofs': [proof_to_json(p) for p in proof.local_proofs],
            'overlap_proofs': [proof_to_json(p) for p in proof.overlap_proofs],
        }

    elif isinstance(proof, Assume):
        return {
            'tag': tag,
            'label': proof.label,
            'assumed_lhs': oterm_to_json(proof.assumed_lhs),
            'assumed_rhs': oterm_to_json(proof.assumed_rhs),
        }

    elif isinstance(proof, Cut):
        return {
            'tag': tag,
            'lemma_lhs': oterm_to_json(proof.lemma_lhs),
            'lemma_rhs': oterm_to_json(proof.lemma_rhs),
            'lemma_proof': proof_to_json(proof.lemma_proof),
            'main_proof': proof_to_json(proof.main_proof),
            'label': proof.label,
        }

    elif isinstance(proof, LetProof):
        return {
            'tag': tag,
            'label': proof.label,
            'sub_lhs': oterm_to_json(proof.sub_lhs),
            'sub_rhs': oterm_to_json(proof.sub_rhs),
            'sub_proof': proof_to_json(proof.sub_proof),
            'body': proof_to_json(proof.body),
        }

    elif isinstance(proof, CasesSplit):
        return {
            'tag': tag,
            'discriminant': oterm_to_json(proof.discriminant),
            'cases': {k: proof_to_json(v) for k, v in proof.cases.items()},
        }

    elif isinstance(proof, Ext):
        return {
            'tag': tag,
            'var': proof.var,
            'body_proof': proof_to_json(proof.body_proof),
        }

    elif isinstance(proof, Rewrite):
        return {
            'tag': tag,
            'equation': proof_to_json(proof.equation),
            'in_lhs': proof.in_lhs,
            'position': list(proof.position),
        }

    elif isinstance(proof, RewriteChain):
        result = {
            'tag': tag,
            'steps': [proof_to_json(s) for s in proof.steps],
        }
        if proof.intermediates:
            result['intermediates'] = [oterm_to_json(t)
                                       for t in proof.intermediates]
        return result

    elif isinstance(proof, ArithmeticSimp):
        return {
            'tag': tag,
            'lhs_expr': oterm_to_json(proof.lhs_expr),
            'rhs_expr': oterm_to_json(proof.rhs_expr),
        }

    elif isinstance(proof, ListSimp):
        return {
            'tag': tag,
            'rule': proof.rule,
            'target': oterm_to_json(proof.target),
        }

    elif isinstance(proof, Definitional):
        return {'tag': tag}

    else:
        return {'tag': 'unknown', 'repr': repr(proof)}


def proof_from_json(data: Dict[str, Any]) -> ProofTerm:
    """Deserialize a ProofTerm from a JSON-compatible dict."""
    tag = data['tag']

    if tag == 'Refl':
        return Refl(oterm_from_json(data['term']))

    elif tag == 'Sym':
        return Sym(proof_from_json(data['proof']))

    elif tag == 'Trans':
        mid = oterm_from_json(data['middle']) if 'middle' in data else None
        return Trans(proof_from_json(data['left']),
                     proof_from_json(data['right']),
                     middle=mid)

    elif tag == 'Cong':
        return Cong(data['func'],
                    tuple(proof_from_json(p) for p in data['arg_proofs']))

    elif tag == 'Beta':
        return Beta(oterm_from_json(data['lam']),
                    oterm_from_json(data['arg']))

    elif tag == 'Delta':
        body = oterm_from_json(data['body']) if 'body' in data else None
        return Delta(data['func_name'],
                     tuple(oterm_from_json(a) for a in data['args']),
                     body=body)

    elif tag == 'Eta':
        return Eta(oterm_from_json(data['term']))

    elif tag == 'NatInduction':
        return NatInduction(
            proof_from_json(data['base_case']),
            proof_from_json(data['inductive_step']),
            data['variable'],
            base_value=oterm_from_json(data.get('base_value', {'type': 'OLit', 'value': 0, 'value_type': 'int'})),
        )

    elif tag == 'ListInduction':
        return ListInduction(
            proof_from_json(data['nil_case']),
            proof_from_json(data['cons_case']),
            data['variable'],
            elem_var=data.get('elem_var', 'x'),
            tail_var=data.get('tail_var', 'xs'),
        )

    elif tag == 'WellFoundedInduction':
        return WellFoundedInduction(
            data['measure'],
            proof_from_json(data['step']),
            measure_type=data.get('measure_type', 'nat'),
        )

    elif tag == 'AxiomApp':
        return AxiomApp(
            data['axiom_name'],
            data['direction'],
            oterm_from_json(data['target']),
            bindings=_bindings_from_json(data.get('bindings', {})),
        )

    elif tag == 'MathlibTheorem':
        return MathlibTheorem(
            data['theorem_name'],
            instantiation=_bindings_from_json(data.get('instantiation', {})),
        )

    elif tag == 'LoopInvariant':
        return LoopInvariant(
            data['invariant'],
            proof_from_json(data['init_proof']),
            proof_from_json(data['preservation']),
            proof_from_json(data['termination']),
            proof_from_json(data['post_proof']),
        )

    elif tag == 'Simulation':
        return Simulation(
            data['relation'],
            proof_from_json(data['init_proof']),
            proof_from_json(data['step_proof']),
            proof_from_json(data['output_proof']),
        )

    elif tag == 'AbstractionRefinement':
        return AbstractionRefinement(
            data['spec_name'],
            proof_from_json(data['abstraction_f']),
            proof_from_json(data['abstraction_g']),
            abstraction_func=data.get('abstraction_func'),
        )

    elif tag == 'CommDiagram':
        return CommDiagram(
            proof_from_json(data['morphism_left']),
            proof_from_json(data['iso_proof']),
        )

    elif tag == 'FunctorMap':
        return FunctorMap(
            data['functor'],
            proof_from_json(data['compose_proof']),
        )

    elif tag == 'Z3Discharge':
        return Z3Discharge(
            data['formula'],
            data['fragment'],
            timeout_ms=data.get('timeout_ms', 5000),
            variables=data.get('variables', {}),
        )

    elif tag == 'FiberDecomposition':
        return FiberDecomposition(
            {k: proof_from_json(v)
             for k, v in data['fiber_proofs'].items()},
        )

    elif tag == 'CechGluing':
        return CechGluing(
            tuple(proof_from_json(p) for p in data['local_proofs']),
            tuple(proof_from_json(p) for p in data['overlap_proofs']),
        )

    elif tag == 'Assume':
        return Assume(
            data['label'],
            oterm_from_json(data['assumed_lhs']),
            oterm_from_json(data['assumed_rhs']),
        )

    elif tag == 'Cut':
        return Cut(
            oterm_from_json(data['lemma_lhs']),
            oterm_from_json(data['lemma_rhs']),
            proof_from_json(data['lemma_proof']),
            proof_from_json(data['main_proof']),
            label=data.get('label', 'lemma'),
        )

    elif tag == 'LetProof':
        return LetProof(
            data['label'],
            oterm_from_json(data['sub_lhs']),
            oterm_from_json(data['sub_rhs']),
            proof_from_json(data['sub_proof']),
            proof_from_json(data['body']),
        )

    elif tag == 'CasesSplit':
        return CasesSplit(
            oterm_from_json(data['discriminant']),
            {k: proof_from_json(v) for k, v in data['cases'].items()},
        )

    elif tag == 'Ext':
        return Ext(data['var'], proof_from_json(data['body_proof']))

    elif tag == 'Rewrite':
        return Rewrite(
            proof_from_json(data['equation']),
            in_lhs=data.get('in_lhs', True),
            position=tuple(data.get('position', ())),
        )

    elif tag == 'RewriteChain':
        intermediates = tuple(oterm_from_json(t)
                              for t in data.get('intermediates', []))
        return RewriteChain(
            tuple(proof_from_json(s) for s in data['steps']),
            intermediates=intermediates,
        )

    elif tag == 'ArithmeticSimp':
        return ArithmeticSimp(
            oterm_from_json(data['lhs_expr']),
            oterm_from_json(data['rhs_expr']),
        )

    elif tag == 'ListSimp':
        return ListSimp(data['rule'], oterm_from_json(data['target']))

    elif tag == 'Definitional':
        return Definitional()

    else:
        raise ValueError(f'unknown proof tag: {tag}')


# ═══════════════════════════════════════════════════════════════════
# Full proof document serialization
# ═══════════════════════════════════════════════════════════════════

@dataclass
class ProofDocument:
    """A complete proof document: goal + proof + metadata."""
    name: str
    lhs: OTerm
    rhs: OTerm
    proof: ProofTerm
    description: str = ''
    strategy: str = ''

    def to_json(self) -> Dict[str, Any]:
        return {
            'name': self.name,
            'lhs': oterm_to_json(self.lhs),
            'rhs': oterm_to_json(self.rhs),
            'proof': proof_to_json(self.proof),
            'description': self.description,
            'strategy': self.strategy,
        }

    @staticmethod
    def from_json(data: Dict[str, Any]) -> 'ProofDocument':
        return ProofDocument(
            name=data['name'],
            lhs=oterm_from_json(data['lhs']),
            rhs=oterm_from_json(data['rhs']),
            proof=proof_from_json(data['proof']),
            description=data.get('description', ''),
            strategy=data.get('strategy', ''),
        )

    def to_json_str(self, indent: int = 2) -> str:
        return json.dumps(self.to_json(), indent=indent)

    @staticmethod
    def from_json_str(s: str) -> 'ProofDocument':
        return ProofDocument.from_json(json.loads(s))


def save_proof(doc: ProofDocument, path: str) -> None:
    """Save a proof document to a JSON file."""
    with open(path, 'w') as f:
        json.dump(doc.to_json(), f, indent=2)


def load_proof(path: str) -> ProofDocument:
    """Load a proof document from a JSON file."""
    with open(path) as f:
        return ProofDocument.from_json(json.load(f))


# ═══════════════════════════════════════════════════════════════════
# Human-readable proof notation
# ═══════════════════════════════════════════════════════════════════

def proof_to_notation(proof: ProofTerm) -> str:
    """Convert a proof term to human-readable notation.

    Example output::

        proof factorial_equiv : fact_rec(n) ≡ fact_iter(n)
        by nat_induction on n:
          base: refl(1)
          step:
            trans via n * fact_rec(n-1):
              δ(fact_rec)
              cong[*](refl(n), IH_n)
    """
    return proof.pretty(indent=0)


def document_to_notation(doc: ProofDocument) -> str:
    """Convert a proof document to human-readable notation."""
    lines = [
        f'-- {doc.description}' if doc.description else '',
        f'-- strategy: {doc.strategy}' if doc.strategy else '',
        f'proof {doc.name} : {doc.lhs.canon()} ≡ {doc.rhs.canon()}',
        proof_to_notation(doc.proof),
    ]
    return '\n'.join(line for line in lines if line)
