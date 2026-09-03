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
        clause = [int(lit) for lit in clause]
        if clause == []:
            raise Unsatisfiable()
        self.clauses.append(clause)

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
        == """p cnf 9 13
1 3 4 0
-1 -4 0
-3 -4 0
1 2 0
1 -4 0
2 -4 0
5 6 7 0
-5 -8 0
-5 -9 0
-6 8 0
-6 -9 0
-7 -8 0
-7 9 0
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
    assert f.to_dimacs() == "p cnf 3 2\n-3 1 2 0\n-3 -1 -2 0\n"


def test_add_unsat_with_conditions():
    f = CNF()
    x, y, p = f.new_vars(3)
    f.add_encoding(x + y >= 5, conditions=[p])
    assert f.to_dimacs() == "p cnf 3 1\n-3 0\n"


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
        [-4, 2, 3],
        [-4, -2, -3],
    ]


def test_literals_from_an_int_var_make_a_nogood():
    """A clause over the literals of integers rules an assignment out."""
    from pindakaas.solver import CaDiCaL, Status

    slv = CaDiCaL()
    x = slv.new_int_var(range(0, 4))
    y = slv.new_int_var([0, 1, 3])

    seen = []
    while True:
        with slv.solve() as result:
            if result.status != Status.SATISFIED:
                break
            assignment = (x.value(result), y.value(result))
        seen.append(assignment)
        slv.add_clause([~x.equals(slv, assignment[0]), ~y.equals(slv, assignment[1])])

    assert sorted(seen) == [(a, b) for a in range(4) for b in [0, 1, 3]]


def test_a_settled_question_gives_a_constant():
    """Where the domain decides, there is no literal to ask for."""
    from pindakaas.encoding import CNF

    f = CNF()
    x = f.new_int_var(range(0, 3))

    assert bool(x.equals(f, 9)) is False
    assert x.equals(f, 9).lit() is None
    assert bool(x.at_least(f, 0)) is True
    assert bool(x.at_most(f, 9)) is True

    reachable = x.at_least(f, 2)
    assert reachable.lit() is not None
    with pytest.raises(ValueError):
        bool(reachable)


def test_asking_without_building_an_encoding():
    """`create=False` answers what the domain or an existing encoding can."""
    from pindakaas.encoding import CNF

    f = CNF()
    x = f.new_int_var([0, 1, 3, 4])

    # The domain settles these, so they cost nothing.
    assert bool(x.at_least(f, 0, create=False)) is True
    assert bool(x.at_least(f, 5, create=False)) is False
    assert bool(x.at_most(f, 4, create=False)) is True
    assert bool(x.at_most(f, -1, create=False)) is False
    assert bool(x.equals(f, 9, create=False)) is False
    assert bool(x.equals(f, 2, create=False)) is False  # the hole

    # These need an encoding, and there is none.
    assert x.at_least(f, 3, create=False) is None
    assert x.at_most(f, 1, create=False) is None
    assert x.equals(f, 3, create=False) is None
    assert f.clauses() == []

    # Asking for it builds the order encoding, which then answers.
    assert x.at_least(f, 3).lit() is not None
    assert f.clauses() != []
    assert x.at_least(f, 3, create=False).lit() is not None

    # Equality wants the direct encoding, which is still not there.
    assert x.equals(f, 3, create=False) is None
    assert x.equals(f, 3).lit() is not None
    assert x.equals(f, 3, create=False).lit() is not None


def test_a_single_value_domain_settles_equality():
    """One value and no other, so no encoding is needed to say which."""
    from pindakaas.encoding import CNF

    f = CNF()
    x = f.new_int_var(range(5, 6))
    assert bool(x.equals(f, 5, create=False)) is True
    assert f.clauses() == []
