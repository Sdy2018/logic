# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/operators.py

"""Syntactic conversion of propositional formulae to use only specific sets of
operators."""

from syntax import *
from semantics import *

TRUE = Formula.parse("(p|~p)")
FALSE = Formula.parse("~(p|~p)")
NAND = Formula.parse("~(p&q)")
NOR = Formula.parse("~(p|q)")
IF = Formula.parse("(~p|q)")
IFF = Formula.parse("((p&q)|~(p|q))")
XOR = Formula.parse("((p&~q)|(~p&q))")
OR = Formula.parse("~(~p&~q)")

NOT_NAND = Formula.parse("(p-&p)")
AND_NAND = Formula.parse("((p-&q)-&(p-&q))")
OR_NAND = Formula.parse("((p-&p)-&(q-&q))")

AND_IN = Formula.parse("~(p->~q)")
OR_IN = Formula.parse("(~p->q)")

NOT_IF = Formula.parse("(p->F)")
OR_IF = Formula.parse("((p->F)->q)")
AND_IF = Formula.parse("((p->(q->F))->F)")

TO_NOT_AND_OR = {"->": IF, "<->": IFF, "+": XOR, "-&": NAND, "-|": NOR, "T": TRUE, "F": FALSE}
TO_NOT_AND = {"|": OR}

NAND_DICT = {"~": NOT_NAND, "&": AND_NAND, "|": OR_NAND}
IMPLIES_NOT_DICT = {"&": AND_IN, "|": OR_IN}
IMPLIES_FALSE_DICT = {"~": NOT_IF, "&": AND_IF, "|": OR_IF}

def to_not_and_or(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'``, ``'&'``, and ``'|'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'``, ``'&'``, and
        ``'|'``.
    """
    # Task 3.5
    return formula.substitute_operators(TO_NOT_AND_OR)


def to_not_and(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'`` and ``'&'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'`` and ``'&'``.
    """
    # Task 3.6a
    return to_not_and_or(formula).substitute_operators(TO_NOT_AND)


def to_nand(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'-&'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'-&'``.
    """
    # Task 3.6b
    return to_not_and_or(formula).substitute_operators(NAND_DICT)

def to_implies_not(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'~'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'~'``.
    """
    # Task 3.6c
    return to_not_and_or(formula).substitute_operators(IMPLIES_NOT_DICT)

def to_implies_false(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'F'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'F'``.
    """
    # Task 3.6d
    return to_not_and_or(formula).substitute_operators(IMPLIES_FALSE_DICT)