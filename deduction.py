# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/deduction.py

"""Useful proof manipulation maneuvers in propositional logic."""

from syntax import *
from proofs import *
from axiomatic_systems import *

def prove_corollary(antecedent_proof: Proof, consequent: Formula,
                    conditional: InferenceRule) -> Proof:
    """Converts the given proof of a formula `antecedent` into a proof of the
    given formula `consequent` by using the given assumptionless inference rule
    of which ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
    specialization.

    Parameters:
        antecedent_proof: valid proof of `antecedent`.
        consequent: formula to prove.
        conditional: assumptionless inference rule of which the assumptionless
            inference rule with conclusion
            ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
            specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proof, via the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP` and `conditional`.
    """
    assert antecedent_proof.is_valid()
    assert InferenceRule([],
                         Formula('->', antecedent_proof.statement.conclusion,
                                 consequent)).is_specialization_of(conditional)
    # Task 5.3a
    previous_proof = antecedent_proof.lines
    this_gorer = InferenceRule("", Formula.parse("(" + str(antecedent_proof.statement.conclusion) + "->" +
                                                 str(consequent) + ")"))
    special = InferenceRule.formula_specialization_map(conditional.conclusion, this_gorer.conclusion)
    after_line = Proof.Line(conditional.conclusion.substitute_variables(special), conditional, ())
    mp_line = Proof.Line(consequent, MP, (len(previous_proof) - 1, len(previous_proof)))
    return Proof(InferenceRule(antecedent_proof.statement.assumptions, consequent),
                 antecedent_proof.rules.union({conditional}),
                 previous_proof + (after_line, mp_line))

def combine_proofs(antecedent1_proof: Proof, antecedent2_proof: Proof,
                   consequent: Formula, double_conditional: InferenceRule) -> \
        Proof:
    """Combines the given proofs of two formulae `antecedent1` and `antecedent2`
    into a proof of the given formula `consequent` by using the given
    assumptionless inference rule of which
    ``('``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
    is a specialization.

    Parameters:
        antecedent1_proof: valid proof of `antecedent1`.
        antecedent2_proof: valid proof of `antecedent2` from the same
            assumptions and inference rules as `antecedent1_proof`.
        consequent: formula to prove.
        double_conditional: assumptionless inference rule of which the
            assumptionless inference rule with conclusion
            ``'(``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
            is a specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and `conditional`.
    """
    assert antecedent1_proof.is_valid()
    assert antecedent2_proof.is_valid()
    assert antecedent1_proof.statement.assumptions == \
           antecedent2_proof.statement.assumptions
    assert antecedent1_proof.rules == antecedent2_proof.rules
    assert InferenceRule(
        [], Formula('->', antecedent1_proof.statement.conclusion,
        Formula('->', antecedent2_proof.statement.conclusion, consequent))
        ).is_specialization_of(double_conditional)
    # Task 5.3b
    new_proof2_lines = []
    for line in antecedent2_proof.lines:
        new_line = line
        if not(line.is_assumption()):
            new_line = Proof.Line(line.formula, line.rule, tuple(map(lambda num: num + len(antecedent1_proof.lines),
                                                                     line.assumptions)))
        new_proof2_lines.append(new_line)
    prev_proofs_lines = antecedent1_proof.lines + tuple(new_proof2_lines)
    this_gorer = InferenceRule("", Formula.parse("(" + str(antecedent1_proof.statement.conclusion) + "->(" +
                                                 str(antecedent2_proof.statement.conclusion) + "->" +
                                                 str(consequent) + "))"))
    special = InferenceRule.formula_specialization_map(double_conditional.conclusion, this_gorer.conclusion)
    after_line = Proof.Line(double_conditional.conclusion.substitute_variables(special), double_conditional, ())
    another_line = InferenceRule("", Formula.parse("(" + str(antecedent2_proof.statement.conclusion) + "->" +
                                 str(consequent) + ")"))

    special2 = InferenceRule.formula_specialization_map(MP.conclusion, another_line.conclusion)
    after_line2 = Proof.Line(MP.conclusion.substitute_variables(special2), MP, (len(antecedent1_proof.lines) - 1,
                             len(antecedent1_proof.lines) + len(antecedent2_proof.lines)))
    mp_line = Proof.Line(consequent, MP, (len(antecedent1_proof.lines) + len(antecedent2_proof.lines) - 1,
                                          len(antecedent1_proof.lines) + len(antecedent2_proof.lines) + 1))
    return Proof(InferenceRule(antecedent1_proof.statement.assumptions,
                               consequent),
                               antecedent2_proof.rules.union(antecedent1_proof.rules.union({double_conditional})),
                               prev_proofs_lines + (after_line, after_line2, mp_line))

def remove_assumption(proof: Proof) -> Proof:
    """Converts a proof of some `conclusion` formula, the last assumption of
    which is an assumption `assumption`, into a proof of
    ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, with at least one assumption, via some
            set of inference rules all of which have no assumptions except
            perhaps `~propositions.axiomatic_systems.MP`.

    Return:
        A valid proof of ``'(``\ `assumptions`\ ``->``\ `conclusion`\ ``)'``
        from the same assumptions as the given proof except the last one, via
        the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`, and
        `~propositions.axiomatic_systems.D`.
    """        
    assert proof.is_valid()
    assert len(proof.statement.assumptions) > 0
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    # Task 5.4
    rules = proof.rules # all the assumptions
    assumption = proof.statement.assumptions[-1] # phi
    other_assumptions = proof.statement.assumptions[:-1] # all other assumptions denoted by * in the lecture (NN)
    new_statement = InferenceRule(other_assumptions, Formula('->', assumption, proof.statement.conclusion)) # new proof statement (without phi)
    lines = []
    table_indexer = []
    for line in proof.lines:
        # case 2 - line is the assumption that we need to prove assumption -> conclusion
        if line.formula == assumption:
            formula = Formula("->", assumption, line.formula)
            lines.append(Proof.Line(formula, I0, ()))
        # case 3 - line is MP
        elif line.rule == MP:
            mp_line1 = lines[table_indexer[line.assumptions[0]]].formula
            mp_line2 = lines[table_indexer[line.assumptions[1]]].formula
            f0 = Formula("->", assumption, line.formula)
            f1 = Formula("->", mp_line1, f0)
            f2 = Formula("->", mp_line2, f1)
            l0 = Proof.Line(f2, D, [])
            l1 = Proof.Line(f1, MP, [table_indexer[line.assumptions[1]], len(lines)])
            l2 = Proof.Line(f0, MP, [table_indexer[line.assumptions[0]], len(lines) + 1])
            lines.append(l0)
            lines.append(l1)
            lines.append(l2)
        # case 1 - line is one of the assumptions in the proof
        # and
        # case 4 - line is inference rule without any assumptions
        else:
            lines.append(line)
            lines.append(Proof.Line(Formula("->", line.formula, (Formula("->", assumption, line.formula))), I1, ()))
            lines.append(Proof.Line(Formula('->', assumption, line.formula), MP, (len(lines) - 2, len(lines) - 1)))
        table_indexer.append(len(lines) - 1)
    return Proof(new_statement, rules.union({MP,I0,I1,D}) ,lines)


def proof_from_inconsistency(proof_of_affirmation: Proof,
                             proof_of_negation: Proof, conclusion: Formula) -> \
        Proof:
    """Combines the given proofs of a formula `affirmation` and its negation
    ``'~``\ `affirmation`\ ``'`` into a proof of the given formula.

    Parameters:
        proof_of_affirmation: valid proof of `affirmation`.
        proof_of_negation: valid proof of ``'~``\ `affirmation`\ ``'`` from the
            same assumptions and inference rules of `proof_of_affirmation`.

    Returns:
        A valid proof of `conclusion` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and
        `~propositions.axiomatic_systems.I2`.
    """
    assert proof_of_affirmation.is_valid()
    assert proof_of_negation.is_valid()
    assert proof_of_affirmation.statement.assumptions == \
           proof_of_negation.statement.assumptions
    assert Formula('~', proof_of_affirmation.statement.conclusion) == \
           proof_of_negation.statement.conclusion
    assert proof_of_affirmation.rules == proof_of_negation.rules
    # Task 5.6
    first_proof_lines = proof_of_affirmation.lines
    second_proof_lines = []
    for line in proof_of_negation.lines:
        if not(line.is_assumption()):
            new_line = Proof.Line(line.formula, line.rule, tuple(map(
                lambda l_number: l_number + len(first_proof_lines), line.assumptions)))
            second_proof_lines.append(new_line)
            continue
        second_proof_lines.append(line)
    i2_line = Proof.Line(Formula('->', proof_of_negation.statement.conclusion,
                                 Formula('->', proof_of_affirmation.statement.conclusion, conclusion)), I2, ())
    mp_once = Proof.Line(Formula('->', proof_of_affirmation.statement.conclusion, conclusion),
                         MP,
                         (len(first_proof_lines) + len(second_proof_lines) - 1,
                          len(first_proof_lines) + len(second_proof_lines)))
    mp_twice = Proof.Line(conclusion, MP, (len(first_proof_lines) - 1,
                                           len(first_proof_lines) + len(second_proof_lines) + 1))
    return Proof(InferenceRule(proof_of_affirmation.statement.assumptions, conclusion),
                 proof_of_negation.rules.union({I2}),
                 first_proof_lines + tuple(second_proof_lines) + (i2_line, mp_once, mp_twice))


def prove_by_contradiction(proof: Proof) -> Proof:
    """Converts the given proof of ``'~(p->p)'``, the last assumption of which
    is an assumption ``'~``\ `formula`\ ``'``, into a proof of `formula` from
    the same assumptions except ``'~``\ `formula`\ ``'``.

    Parameters:
        proof: valid proof of ``'~(p->p)'`` to convert, the last assumption of
            which is of the form ``'~``\ `formula`\ ``'``, via some set of
            inference rules all of which have no assumptions except perhaps
            `~propositions.axiomatic_systems.MP`.

    Return:
        A valid proof of `formula` from the same assumptions as the given proof
        except the last one, via the same inference rules as the given proof and
        in addition `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    assert proof.is_valid()
    assert proof.statement.conclusion == Formula.parse('~(p->p)')
    assert len(proof.statement.assumptions) > 0
    assert proof.statement.assumptions[-1].root == '~'
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    # Task 5.7
    proving = proof.statement.assumptions[-1].first
    statement = InferenceRule(proof.statement.assumptions[:-1], proving)
    rules = proof.rules.union({I0, I1, D, MP, N})
    new_proof = remove_assumption(proof)
    lines = list(new_proof.lines)
    lines.append(Proof.Line(N.specialize({'q': proving, 'p': I0.conclusion}).conclusion, N, ()))
    lines.append(Proof.Line(Formula('->', I0.conclusion, proving), MP, (len(lines) - 2, len(lines) - 1)))
    lines.append(Proof.Line(I0.conclusion, I0, ()))
    lines.append(Proof.Line(proving, MP, (len(lines) - 1, len(lines) - 2)))
    return Proof(statement, rules, lines)
