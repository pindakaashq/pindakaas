from itertools import product
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
from pindakaas.solver import CaDiCaL, Status


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


# Which encoder takes which constraint. An encoder is dispatched separately for
# each shape a constraint can aggregate to, so one of those arms going missing
# shows up as `InvalidEncoder` for that shape alone and nowhere else.
LINEAR = [
    Encoder.ADDER,
    Encoder.DECISION_DIAGRAM,
    Encoder.MIXED_RADIX,
    Encoder.SEQUENTIAL_COUNTER,
    Encoder.SORTING_NETWORK,
    Encoder.TOTALIZER,
    Encoder.WATCHDOG,
]
AT_MOST_ONE = LINEAR + [
    Encoder.BITWISE,
    Encoder.LADDER,
    Encoder.PAIRWISE,
    Encoder.PRODUCT,
]


@pytest.mark.parametrize("encoder", LINEAR)
def test_every_linear_encoder_takes_a_weighted_sum(encoder):
    f = CNF()
    x, y, z = f.new_vars(3)
    f.add_encoding(x * 2 + y * 3 + z * 4 <= 5, encoder=encoder)


@pytest.mark.parametrize("encoder", LINEAR)
def test_every_counting_encoder_takes_a_cardinality_constraint(encoder):
    f = CNF()
    x, y, z = f.new_vars(3)
    f.add_encoding(x + y + z <= 2, encoder=encoder)


@pytest.mark.parametrize("encoder", AT_MOST_ONE)
def test_every_at_most_one_encoder_takes_an_at_most_one_constraint(encoder):
    f = CNF()
    x, y, z = f.new_vars(3)
    f.add_encoding(x + y + z <= 1, encoder=encoder)


# The options that change the clauses on the shapes below. `cutoff`,
# `consistency`, and `propagation` leave them as they are, in Rust as well.
CHANGING = [
    (Encoder.MIXED_RADIX, {"base": [3, 2]}),
    (Encoder.WATCHDOG, {"local": True}),
    (Encoder.WATCHDOG, {"sorting_networks": True}),
    (Encoder.SORTING_NETWORK, {"strategy": "recursive"}),
    (Encoder.PRODUCT, {"pairwise_cutoff": 2}),
]

# Every option each encoder takes, with a value other than its default.
OPTIONS = [
    *product(
        [
            Encoder.DECISION_DIAGRAM,
            Encoder.MIXED_RADIX,
            Encoder.SEQUENTIAL_COUNTER,
            Encoder.TOTALIZER,
            Encoder.WATCHDOG,
        ],
        [{"consistency": True}, {"cutoff": 0}, {"propagation": False}],
    ),
    *CHANGING,
    (Encoder.WATCHDOG, {"local": True, "sorting_networks": True}),
    (Encoder.WATCHDOG, {"consistency": True, "sorting_networks": True}),
    (Encoder.SORTING_NETWORK, {"consistency": True}),
    (Encoder.SORTING_NETWORK, {"strategy": "direct"}),
    (Encoder.SORTING_NETWORK, {"strategy": "mixed"}),
]


def weighted_sum(db, encoder, extra=0):
    """Literals and a sum over them the encoder takes, with its bound."""
    if encoder == Encoder.PRODUCT:
        coeffs, k = [1] * (5 + extra), 1
    else:
        coeffs, k = [2, 3, 5, 4, 6, 2, 3, 5, 4][: 5 + extra], 9 + extra
    xs = list(db.new_vars(len(coeffs)))
    expr = sum((x * c for x, c in zip(xs[1:], coeffs[1:])), xs[0] * coeffs[0])
    return xs, coeffs, expr, k


@pytest.mark.parametrize("encoder, options", OPTIONS)
@pytest.mark.parametrize("equality", [False, True])
def test_options_keep_every_solution(encoder, options, equality):
    """Each assignment of the terms is a model exactly if it meets the bound."""
    slv = CaDiCaL()
    xs, coeffs, expr, k = weighted_sum(slv, encoder)
    slv.add_encoding(expr == k if equality else expr <= k, encoder, **options)
    for values in product([False, True], repeat=len(xs)):
        total = sum(c for c, v in zip(coeffs, values) if v)
        expected = total == k if equality else total <= k
        assumptions = [x if v else ~x for x, v in zip(xs, values)]
        with slv.solve(assumptions=assumptions) as result:
            assert (result.status == Status.SATISFIED) == expected, values


@pytest.mark.parametrize("db", [CNF, CustomDB])
@pytest.mark.parametrize("encoder, options", CHANGING)
def test_options_change_the_encoding(db, encoder, options):
    def clauses(**options):
        f = db()
        _, _, expr, k = weighted_sum(f, encoder, extra=4)
        f.add_encoding(expr <= k, encoder, **options)
        return f.to_dimacs() if isinstance(f, CNF) else f.clauses

    assert clauses(**options) != clauses()


def test_an_option_is_checked_when_aggregation_settles_the_constraint():
    """A bound no assignment reaches needs no encoder, but the options are read."""
    f = CNF()
    x, y = f.new_vars(2)
    with pytest.raises(InvalidEncoder, match="sorting_network"):
        f.add_encoding(x + y <= 2, Encoder.WATCHDOG, sorting_network=True)


def test_options_reach_the_default_encoder():
    """The totalizer is the default for a weighted sum, and takes `cutoff`."""
    f = CNF()
    x, y, z = f.new_vars(3)
    f.add_encoding(x * 2 + y * 3 + z * 4 <= 5, cutoff=0)
    with pytest.raises(InvalidEncoder, match="TOTALIZER"):
        f.add_encoding(x * 2 + y * 3 + z * 4 <= 5, local=True)


@pytest.mark.parametrize("encoder", AT_MOST_ONE + [Encoder.TSEITIN])
def test_an_option_the_encoder_does_not_take_is_invalid(encoder):
    f = CNF()
    x, y, z = f.new_vars(3)
    con = x & y if encoder == Encoder.TSEITIN else x + y + z <= 1
    with pytest.raises(InvalidEncoder, match="sorting_network"):
        f.add_encoding(con, encoder, sorting_network=True)
    assert f.clauses() == []


@pytest.mark.parametrize(
    "encoder, options",
    [
        (Encoder.MIXED_RADIX, {"base": []}),
        (Encoder.MIXED_RADIX, {"base": [3, 1]}),
        (Encoder.PRODUCT, {"pairwise_cutoff": 1}),
        (Encoder.PRODUCT, {"pairwise_cutoff": -1}),
        (Encoder.SORTING_NETWORK, {"strategy": "bubble"}),
    ],
)
def test_an_invalid_option_value_is_refused(encoder, options):
    f = CNF()
    x, y, z = f.new_vars(3)
    with pytest.raises(ValueError):
        f.add_encoding(x + y + z <= 1, encoder, **options)


def test_encode_bool_lin_default():
    f = CNF()
    x, y, z = f.new_vars(3)
    f += x * 3 + y * 2 + z >= 3
    x, y, z = f.new_vars(3)
    f.add_encoding(x + y + z == 1)
    assert (
        f.to_dimacs()
        == """p cnf 9 10
-5 4 0
-6 5 0
2 5 0
3 4 0
3 2 6 0
-4 1 0
7 8 9 0
-7 -8 0
-7 -9 0
-8 -9 0
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
    assert f.to_dimacs() == "h 1 2 0\n1 1 0\n2 2 0\n"


def test_clauses_as_int():
    f = CNF()
    x, y, z = f.new_vars(3)
    f.add_clause([x, ~y])
    f.add_encoding(2 * x + 3 * y + 4 * z <= 5)
    assert f._clauses_as_int()[0] == [1, -2]
    assert f._clauses_as_int() == [[int(lit) for lit in c] for c in f.clauses()]


def test_wcnf_clauses_as_int_are_hard():
    f = WCNF()
    x, y = f.new_vars(2)
    f.add_clause([~x, y])
    f.add_weighted_clause([x], 1)
    assert f._clauses_as_int() == [[-1, 2]]


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


def test_custom_db_without_conditions():
    f = CustomDB()
    x, y = f.new_vars(2)
    f.add_encoding(x ^ y)
    assert f.clauses == [[1, 2], [-1, -2]]


def test_custom_db_conditions_from_a_generator():
    f = CustomDB()
    x, y, p = f.new_vars(3)
    f.add_encoding(x ^ y, conditions=(lit for lit in [p]))
    assert f.clauses == [[-3, 1, 2], [-3, -1, -2]]


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

    assert x.equals(f, 9).value() is False
    assert x.equals(f, 9).lit() is None
    assert x.at_least(f, 0).value() is True
    assert x.at_most(f, 9).value() is True

    reachable = x.at_least(f, 2)
    assert reachable.lit() is not None
    assert reachable.value() is None


def test_asking_without_building_an_encoding():
    """`create=False` answers what the domain or an existing encoding can."""
    from pindakaas.encoding import CNF

    f = CNF()
    x = f.new_int_var([0, 1, 3, 4])

    # The domain settles these, so they cost nothing.
    assert x.at_least(f, 0, create=False).value() is True
    assert x.at_least(f, 5, create=False).value() is False
    assert x.at_most(f, 4, create=False).value() is True
    assert x.at_most(f, -1, create=False).value() is False
    assert x.equals(f, 9, create=False).value() is False
    assert x.equals(f, 2, create=False).value() is False  # the hole

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


def test_an_order_encoding_settles_equality_at_the_ends():
    """Taking the greatest value is reaching it, and the least is not passing it."""
    from pindakaas.encoding import CNF

    f = CNF()
    x = f.new_int_var(range(0, 4))
    assert x.at_least(f, 2).lit() is not None  # builds the order encoding
    clauses = f.clauses()

    # The order literals answer both ends without a direct encoding.
    assert x.equals(f, 3, create=False).lit() is not None
    assert x.equals(f, 0, create=False).lit() is not None
    assert f.clauses() == clauses

    # Anything between them still needs the direct encoding.
    assert x.equals(f, 1, create=False) is None


def test_a_single_value_domain_settles_equality():
    """One value and no other, so no encoding is needed to say which."""
    from pindakaas.encoding import CNF

    f = CNF()
    x = f.new_int_var(range(5, 6))
    assert x.equals(f, 5, create=False).value() is True
    assert f.clauses() == []
