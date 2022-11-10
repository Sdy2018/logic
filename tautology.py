# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/tautology.py

"""The Tautology Theorem and its implications."""

from typing import List, Union

from logic_utils import frozendict

from syntax import *
from proofs import *
from deduction import *
from semantics import *
# from propositions.operators import *
from axiomatic_systems import *

def proof_merger(first_proof: Proof, second_proof: Proof) -> List[Proof.Line]:
    """
    Combine two proof into one and and return the lines
    :param first_proof: first proof
    :param second_proof: second
    :return: list of proof lines
    """
    proof_lines = []
    for line in second_proof.lines:
        new_line = line
        if not(line.is_assumption()):
            new_line = Proof.Line(line.formula, line.rule, tuple(map(lambda num: num + len(first_proof.lines),
                                                                     line.assumptions)))
        proof_lines.append(new_line)
    return list(first_proof.lines) + proof_lines

def formulae_capturing_model(model: Model) -> List[Formula]:
    """Computes the formulae that capture the given model: ``'``\ `x`\ ``'``
    for each variable `x` that is assigned the value ``True`` in the given
    model, and ``'~``\ `x`\ ``'`` for each variable x that is assigned the value
    ``False``.

    Parameters:
        model: model to construct the formulae for.

    Returns:
        A list of the constructed formulae, ordered alphabetically by variable
        name.

    Examples:
        >>> formulae_capturing_model({'p2': False, 'p1': True, 'q': True})
        [p1, ~p2, q]
    """
    assert is_model(model)
    # Task 6.1a
    return list(map(lambda x: Formula.parse(x) if model[x] else Formula.parse("~"+x), sorted(variables(model))))

def prove_in_model(formula: Formula, model:Model) -> Proof:
    """Either proves the given formula or proves its negation, from the formulae
    that capture the given model.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, whose affirmation or negation is to prove.
        model: model from whose formulae to prove.

    Returns:
        If the given formula evaluates to ``True`` in the given model, then
        a proof of the formula, otherwise a proof of ``'~``\ `formula`\ ``'``.
        The returned proof is from the formulae that capture the given model, in
        the order returned by `formulae_capturing_model`\ ``(``\ `model`\ ``)``,
        via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    assert formula.operators().issubset({'->', '~'})
    assert is_model(model)
    # Task 6.1b
    assum = formulae_capturing_model(model)
    if len(formula.variables()) == 1 and str(formula) in model.keys():
        if model[str(formula)]:
            return Proof(InferenceRule(assum, formula), AXIOMATIC_SYSTEM, [Proof.Line(formula)])
        neg_formula = Formula.parse("~" + str(formula))
        return Proof(InferenceRule(assum, neg_formula),
                     AXIOMATIC_SYSTEM, [Proof.Line(neg_formula)])
    elif str(formula)[0] == "~":
        if evaluate(formula, model):
            return prove_in_model(Formula.parse(str(formula)[1:]), model)
        else:
            psi_proof = prove_in_model(Formula.parse(str(formula)[1:]), model)
            psi_proof_lines = psi_proof.lines
            specialized_nn = NN.conclusion.substitute_variables({'p': psi_proof.statement.conclusion})
            line_nn = Proof.Line(specialized_nn, NN, ())
            line_mp = Proof.Line(specialized_nn.second, MP, (len(psi_proof_lines) - 1, len(psi_proof_lines)))
            return Proof(InferenceRule(assum,
                                       specialized_nn.second),
                         AXIOMATIC_SYSTEM,
                         list(psi_proof_lines) + [line_nn] + [line_mp])
    else:
        if evaluate(formula, model):
            if not evaluate(formula.first, model):  # case 1
                phi1_proof = prove_in_model(formula.first, model)
                phi1_proof_lines = phi1_proof.lines
                specialized_i2 = I2.conclusion.substitute_variables({'p': formula.first,
                                                                     'q': formula.second})
                line_i2 = Proof.Line(specialized_i2, I2, ())
                line_mp = Proof.Line(specialized_i2.second, MP, (len(phi1_proof_lines) - 1, len(phi1_proof_lines)))
                return Proof(InferenceRule(assum,
                                           specialized_i2.second),
                             AXIOMATIC_SYSTEM,
                             list(phi1_proof_lines) + [line_i2] + [line_mp])
            else:
                phi2_proof = prove_in_model(formula.second, model)
                phi2_proof_lines = phi2_proof.lines
                specialized_i1 = I1.conclusion.substitute_variables({'q': phi2_proof.statement.conclusion,
                                                                     'p': formula.first})
                line_i2 = Proof.Line(specialized_i1, I1, ())
                line_mp = Proof.Line(specialized_i1.second, MP, (len(phi2_proof_lines) - 1, len(phi2_proof_lines)))
                return Proof(InferenceRule(assum,
                                           specialized_i1.second),
                             AXIOMATIC_SYSTEM,
                             list(phi2_proof_lines) + [line_i2] + [line_mp])
        else:
            phi1_proof = prove_in_model(formula.first, model)
            phi1_proof_lines = phi1_proof.lines
            phi2_proof = prove_in_model(formula.second, model)
            phi2_proof_lines = phi2_proof.lines
            specialized_ni = NI.conclusion.substitute_variables({'p': formula.first,
                                                                 'q': formula.second})
            line_ni = Proof.Line(specialized_ni, NI, ())
            line_mp1 = Proof.Line(specialized_ni.second, MP,
                                  (len(phi1_proof_lines) - 1, len(phi1_proof_lines) + len(phi2_proof_lines)))
            line_mp2 = Proof.Line(specialized_ni.second.second, MP,
                                  (len(phi1_proof_lines) + len(phi2_proof_lines) - 1,
                                   len(phi1_proof_lines) + len(phi2_proof_lines) + 1))
            return Proof(InferenceRule(assum,
                                       line_mp2.formula),
                         AXIOMATIC_SYSTEM,
                         proof_merger(phi1_proof, phi2_proof) + [line_ni, line_mp1, line_mp2])

def reduce_assumption(proof_from_affirmation: Proof,
                      proof_from_negation: Proof) -> Proof:
    """Combines the given two proofs, both of the same formula `conclusion` and
    from the same assumptions except that the last assumption of the latter is
    the negation of that of the former, into a single proof of `conclusion` from
    only the common assumptions.

    Parameters:
        proof_from_affirmation: valid proof of `conclusion` from one or more
            assumptions, the last of which is an assumption `assumption`.
        proof_of_negation: valid proof of `conclusion` from the same assumptions
            and inference rules of `proof_from_affirmation`, but with the last
            assumption being ``'~``\ `assumption` ``'`` instead of `assumption`.

    Returns:
        A valid proof of `conclusion` from only the assumptions common to the
        given proofs (i.e., without the last assumption of each), via the same
        inference rules of the given proofs and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.R`.

    Examples:
        If the two given proofs are of ``['p', 'q'] ==> '(q->p)'`` and of
        ``['p', '~q'] ==> ('q'->'p')``, then the returned proof is of
        ``['p'] ==> '(q->p)'``.
    """
    assert proof_from_affirmation.is_valid()
    assert proof_from_negation.is_valid()
    assert proof_from_affirmation.statement.conclusion == \
           proof_from_negation.statement.conclusion
    assert len(proof_from_affirmation.statement.assumptions) > 0
    assert len(proof_from_negation.statement.assumptions) > 0
    assert proof_from_affirmation.statement.assumptions[:-1] == \
           proof_from_negation.statement.assumptions[:-1]
    assert Formula('~', proof_from_affirmation.statement.assumptions[-1]) == \
           proof_from_negation.statement.assumptions[-1]
    assert proof_from_affirmation.rules == proof_from_negation.rules
    # Task 6.2
    proof1 = remove_assumption(proof_from_affirmation)
    proof2 = remove_assumption(proof_from_negation)
    proof_lines = proof_merger(proof1, proof2)
    specialize_r = R.conclusion.substitute_variables({'p': proof_from_affirmation.statement.conclusion,
                                                      'q': proof1.statement.conclusion.first})
    line_r = Proof.Line(specialize_r, R, ())
    line_mp1 = Proof.Line(specialize_r.second, MP, (len(proof1.lines) - 1, len(proof_lines)))
    line_mp2 = Proof.Line(specialize_r.second.second, MP, (len(proof_lines) - 1, len(proof_lines) + 1))
    return Proof(InferenceRule(proof1.statement.assumptions, specialize_r.second.second),
                 AXIOMATIC_SYSTEM,
                 proof_lines + [line_r, line_mp1, line_mp2])

def prove_tautology(tautology: Formula, model: Model = frozendict()) -> Proof:
    """Proves the given tautology from the formulae that capture the given
    model.

    Parameters:
        tautology: tautology that contains no constants or operators beyond
            ``'->'`` and ``'~'``, to prove.
        model: model over a (possibly empty) prefix (with respect to the
            alphabetical order) of the variables of `tautology`, from whose
            formulae to prove.

    Returns:
        A valid proof of the given tautology from the formulae that capture the
        given model, in the order returned by
        `formulae_capturing_model`\ ``(``\ `model`\ ``)``, via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.

    Examples:
        If the given model is the empty dictionary, then the returned proof is
        of the given tautology from no assumptions.
    """
    assert is_tautology(tautology)
    assert tautology.operators().issubset({'->', '~'})
    assert is_model(model)
    assert sorted(tautology.variables())[:len(model)] == sorted(model.keys())
    # Task 6.3a
    if tautology.variables().issubset(model.keys()):
        return prove_in_model(tautology, model)
    model = dict(model)
    sorted_vars = sorted(list(tautology.variables()))
    for variable in sorted_vars:
        if variable not in model.keys():
            model[variable] = True
            model_t = model.copy()
            model[variable] = False
            model_f = model.copy()
            proof_t = prove_tautology(tautology, model_t)
            proof_f = prove_tautology(tautology, model_f)
            res_proof = reduce_assumption(proof_t, proof_f)
            return res_proof


def proof_or_counterexample(formula: Formula) -> Union[Proof, Model]:
    """Either proves the given formula or finds a model in which it does not
    hold.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, to either prove or find a counterexample for.

    Returns:
        If the given formula is a tautology, then an assumptionless proof of the
        formula via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`,
        otherwise a model in which the given formula does not hold.
    """
    assert formula.operators().issubset({'->', '~'})
    # Task 6.3b
    if is_tautology(formula):
        return prove_tautology(formula)
    return [m for m in all_models(list(formula.variables())) if not evaluate(formula, m)][0]


def encode_as_formula(rule: InferenceRule) -> Formula:
    """Encodes the given inference rule as a formula consisting of a chain of
    implications.

    Parameters:
        rule: inference rule to encode.

    Returns:
        The formula encoding the given rule.

    Examples:
        >>> encode_as_formula(InferenceRule([Formula('p1'), Formula('p2'),
        ...                                  Formula('p3'), Formula('p4')],
        ...                                 Formula('q')))
        (p1->(p2->(p3->(p4->q))))
        >>> encode_as_formula(InferenceRule([], Formula('q')))
        q
    """
    # Task 6.4a
    if not rule.assumptions:
        return rule.conclusion
    elif len(rule.assumptions) == 1:
        return Formula('->', rule.assumptions[0], rule.conclusion)
    else:
        new_rule = InferenceRule(rule.assumptions[1:], rule.conclusion)
        return Formula('->', rule.assumptions[0], encode_as_formula(new_rule))


def prove_sound_inference(rule: InferenceRule) -> Proof:
    """Proves the given sound inference rule.

    Parameters:
        rule: sound inference rule whose assumptions and conclusion that contain
            no constants or operators beyond ``'->'`` and ``'~'``, to prove.

    Returns:
        A valid assumptionless proof of the given sound inference rule via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    assert is_sound_inference(rule)
    for formula in rule.assumptions + (rule.conclusion,):
        assert formula.operators().issubset({'->', '~'})
    # Task 6.4b
    formula = encode_as_formula(rule)
    proof = prove_tautology(formula, {})
    offset = len(proof.lines)
    lines = list(proof.lines)
    for assumption in rule.assumptions:
        specialization = MP.conclusion.substitute_variables({'q': formula.second})
        line_assumption = Proof.Line(formula.first)
        line_mp = Proof.Line(specialization, MP, (offset, offset - 1))
        lines += [line_assumption, line_mp]
        offset += 2
        formula = formula.second
    return Proof(InferenceRule(rule.assumptions, rule.conclusion),
                 AXIOMATIC_SYSTEM,
                 lines)


def model_or_inconsistency(formulae: List[Formula]) -> Union[Model, Proof]:
    """Either finds a model in which all the given formulae hold, or proves
    ``'~(p->p)'`` from these formula.

    Parameters:
        formulae: formulae that use only the operators ``'->'`` and ``'~'``, to
            either find a model for or prove ``'~(p->p)'`` from.

    Returns:
        A model in which all of the given formulae hold if such exists,
        otherwise a proof of '~(p->p)' from the given formulae via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    for formula in formulae:
        assert formula.operators().issubset({'->', '~'})
    # Task 6.5
    formulae = list(formulae)
    new_formula = formulae[0]
    for formula in formulae[1:]:
        new_formula = Formula('&', new_formula, formula)
    for model in all_models(list(new_formula.variables())):
        if evaluate(new_formula, model):
            return model
    return prove_sound_inference(InferenceRule(formulae, Formula.parse('~(p->p)')))

def prove_in_model_full(formula: Formula, model: Model) -> Proof:
    """Either proves the given formula or proves its negation, from the formulae
    that capture the given model.

    Parameters:
        formula: formula that contains no operators beyond ``'->'``, ``'~'``,
            ``'&'``, and ``'|'``, whose affirmation or negation is to prove.
        model: model from whose formulae to prove.

    Returns:
        If the given formula evaluates to ``True`` in the given model, then
        a proof of the formula, otherwise a proof of ``'~``\ `formula`\ ``'``.
        The returned proof is from the formulae that capture the given model, in
        the order returned by `formulae_capturing_model`\ ``(``\ `model`\ ``)``,
        via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM_FULL`.
    """
    assert formula.operators().issubset({'T', 'F', '->', '~', '&', '|'})
    assert is_model(model)
    # Optional Task 6.6
