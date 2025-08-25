from typing import Iterable

import pytest
from pindakaas import (
    CNF,
    WCNF,
    ClauseDatabase,
    Encoder,
    InvalidEncoder,
    Lit,
    Unsatisfiable,
)
from pindakaas.encoding import VarRange


class CustomDB(ClauseDatabase):
    clauses: list[list[int]]
    next_var: int

    def __init__(self):
        self.clauses = []
        self.next_var = 1

    def add_clause(self, clause: Iterable[Lit]):
        self.clauses.append([int(lit) for lit in clause])

    def new_var_range(self, n: int) -> VarRange:
        start = self.next_var
        self.next_var += n
        return VarRange(Lit.from_raw(start), Lit.from_raw(self.next_var - 1))


def test_unsat():
    f = CNF()
    with pytest.raises(Unsatisfiable):
        f.add_clause([])


def test_cnf():
    f = CNF()
    x, y = f.new_vars(2)
    assert list(f.variables()) == [x, y]
    f.add_clause([x, y])
    assert f.to_dimacs() == "p cnf 2 1\n1 2 0\n"
    assert f.clauses() == [[x, y]]


def test_encode_bool_lin_unsat():
    f = CNF()
    x, y, z = f.new_vars(3)
    with pytest.raises(Unsatisfiable):
        f += x * 3 + y * 2 + z >= 10


def test_invalid_encoder():
    f = CNF()
    x, y, z = f.new_vars(3)
    with pytest.raises(InvalidEncoder):
        f.add_encoding(x * 3 + y * 2 + z >= 3, encoder=Encoder.PAIRWISE)


def test_encode_bool_lin_default():
    f = CNF()
    x, y, z = f.new_vars(3)
    f += x * 3 + y * 2 + z >= 3
    x, y, z = f.new_vars(3)
    f.add_encoding(x + y + z == 1)
    assert (
        f.to_dimacs()
        == """p cnf 11 13
2 5 0
3 4 0
3 2 6 0
-4 1 0
-5 1 0
-6 1 0
7 8 9 0
-7 -10 0
-7 -11 0
-8 10 0
-8 -11 0
-9 -10 0
-9 11 0
"""
    )


def test_encode_formula():
    f = CNF()
    x, y, z = f.new_vars(3)
    f += x ^ z
    f.add_encoding(x == y, Encoder.TSEITIN)
    f.add_encoding(x & y)
    assert f.to_dimacs() == "p cnf 3 6\n1 3 0\n-1 -3 0\n-1 2 0\n1 -2 0\n1 0\n2 0\n"


def test_wcnf():
    f = WCNF()
    x, y = f.new_vars(2)
    f.add_clause([x, y])
    f.add_weighted_clause([x], 1)
    f.add_weighted_clause([y], 2)
    assert f.to_dimacs() == "p wcnf 2 3 4\n4 1 2 0\n1 1 0\n2 2 0\n"


def test_conditions():
    f = CNF()
    x, y, p = f.new_vars(3)
    f.add_encoding(x ^ y, conditions=[p])
    assert f.to_dimacs() == "p cnf 3 2\n3 1 2 0\n3 -1 -2 0\n"


def test_custom_db():
    f = CustomDB()
    assert f.new_var() == Lit.from_raw(1)
    x, y, p = f.new_vars(3)
    assert [x, y, p] == [
        Lit.from_raw(2),
        Lit.from_raw(3),
        Lit.from_raw(4),
    ]

    f.add_encoding(x ^ y, conditions=[p])
    assert f.clauses == [
        [4, 2, 3],
        [4, -2, -3],
    ]
