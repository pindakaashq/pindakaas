from itertools import product

import pindakaas
import pytest
from pindakaas import CNF, IntVar, Lit


class Assignment:
    """A truth value for every literal, of the shape :meth:`IntVar.value` reads."""

    def __init__(self, true: set):
        self.true = true

    def value(self, lit: Lit) -> bool:
        return int(lit) in self.true


def solutions(f: CNF, *variables: IntVar) -> list:
    """Every assignment satisfying `f`, read back as values of `variables`.

    Enumerated rather than solved, so that a test says what the clauses allow
    rather than what one solver happened to return.
    """
    literals = [int(v) for v in f.variables()]
    found = []
    for bits in product([False, True], repeat=len(literals)):
        true = {lit if b else -lit for lit, b in zip(literals, bits)}
        if all(any(int(lit) in true for lit in clause) for clause in f.clauses()):
            a = Assignment(true)
            found.append(tuple(v.value(a) for v in variables))
    return sorted(set(found))


def test_int_var_bounds():
    f = CNF()
    x = f.new_int_var(range(-2, 6))
    assert (x.min(), x.max(), x.card()) == (-2, 5, 8)


def test_int_var_str_tells_one_variable_from_another():
    # Two variables over the same values are still two variables, so what is
    # shown is where each is held rather than what it can be. The address says
    # nothing across runs: only which occurrences are the same variable.
    f = CNF()
    x, y = f.new_int_var(range(0, 4)), f.new_int_var(range(0, 4))
    assert str(x).startswith("y@") and str(y).startswith("y@")
    assert str(x) != str(y), "the same domain is not the same variable"
    assert str(x * 2 + y) == f"2*{x} + {y}"


@pytest.mark.parametrize(
    "domain",
    [
        [0, 1, 3],
        {3, 1, 0},
        (v for v in [3, 0, 1, 1]),
        [range(0, 2), range(3, 4)],
        [range(0, 2), 3],
    ],
)
def test_int_var_domain_forms(domain):
    # A range, the values themselves, or several ranges: all of them say what
    # the variable can be, and a hole is a hole however it was written.
    x = CNF().new_int_var(domain)
    assert (x.min(), x.max(), x.card()) == (0, 3, 3)


@pytest.mark.parametrize("domain", [range(0, 0), [], [range(2, 2)]])
def test_int_var_empty_domain(domain):
    with pytest.raises(ValueError):
        CNF().new_int_var(domain)


def test_int_var_range_is_not_enumerated():
    # A range crosses into the library as its two ends, so declaring a domain
    # of a million values costs nothing until something is encoded over it.
    x = CNF().new_int_var(range(0, 2**20))
    assert (x.min(), x.max(), x.card()) == (0, 2**20 - 1, 2**20)


def test_int_var_holes_are_kept():
    # The holes are the point: a solution can only be a value of the domain,
    # with no constraint posted to say so.
    f = CNF()
    x = f.new_int_var([1, 2, 5, 6])
    y = f.new_int_var([0, 3])
    f += x + y <= 5
    assert solutions(f, x, y) == [(1, 0), (1, 3), (2, 0), (2, 3), (5, 0)]


def test_int_var_linear():
    f = CNF()
    x = f.new_int_var(range(0, 4))
    y = f.new_int_var(range(1, 3))
    f += x * 2 + y <= 5
    assert solutions(f, x, y) == sorted(
        (i, j) for i in range(4) for j in (1, 2) if 2 * i + j <= 5
    )


def test_int_var_bare_comparison():
    f = CNF()
    x = f.new_int_var(range(0, 4))
    f += x >= 2
    assert solutions(f, x) == [(2,), (3,)]


def test_int_var_with_boolean_terms():
    f = CNF()
    x = f.new_int_var(range(0, 3))
    b = f.new_var()
    f += x + b * 2 == 3
    assert solutions(f, x) == [(1,)], "the literal is worth 2, leaving 1 for x"


def test_int_var_solved():
    slv = pindakaas.solver.CaDiCaL()
    x = slv.new_int_var(range(0, 8))
    y = slv.new_int_var(range(0, 8))
    slv += x + y == 7
    slv += x - y >= 5
    with slv.solve() as result:
        assert result.status == pindakaas.solver.Status.SATISFIED
        vx, vy = x.value(result), y.value(result)
        assert vx + vy == 7 and vx - vy >= 5, f"{vx} and {vy} do not solve it"


@pytest.mark.parametrize("values", [range(0, 4), [0, 1, 3], [-3, -1, 4]])
def test_int_var_from_order_literals(values):
    f = CNF()
    x = f.int_var_from_order_literals(values, f.new_vars(len(values) - 1))
    assert (x.min(), x.max(), x.card()) == (values[0], values[-1], len(values))
    x.constrain(f)
    assert solutions(f, x) == [(v,) for v in values]


@pytest.mark.parametrize("values", [range(0, 4), [0, 1, 3], [-3, -1, 4]])
def test_int_var_from_direct_literals(values):
    f = CNF()
    x = f.int_var_from_direct_literals(values, f.new_vars(len(values)))
    x.constrain(f)
    assert solutions(f, x) == [(v,) for v in values]


@pytest.mark.parametrize("values", [range(0, 4), [0, 1, 3], [-3, -1, 4]])
def test_int_var_from_binary_literals(values):
    f = CNF()
    span = values[-1] - values[0]
    x = f.int_var_from_binary_literals(
        values, f.new_vars(span.bit_length()), counts_from=values[0]
    )
    x.constrain(f)
    assert solutions(f, x) == [(v,) for v in values]


def test_int_var_literals_are_taken_at_their_word():
    # Nothing is added to make the literals mean what they are said to mean,
    # because they nearly always come from a structure that has seen to it
    # already. Asking is what `constrain` is for.
    f = CNF()
    x = f.int_var_from_order_literals([0, 1, 3], f.new_vars(2))
    assert f.clauses() == [], "no clause was added to make the literals mean this"

    x.constrain(f)
    assert len(f.clauses()) == 1, "asking is what adds the one it takes"
    assert solutions(f, x) == [(0,), (1,), (3,)]


def test_int_var_from_literals_used_in_a_constraint():
    f = CNF()
    x = f.int_var_from_order_literals([0, 2, 4], f.new_vars(2))
    x.constrain(f)
    f += x * 3 <= 7
    assert solutions(f, x) == [(0,), (2,)]


def test_int_var_shares_its_literals():
    # One variable used twice: the second constraint reads the encoding the
    # first one built. Were it to make an encoding of its own, the two would
    # be free to disagree and the answer would not be the values both allow.
    f = CNF()
    x = f.new_int_var(range(0, 6))
    f += x >= 2
    f += x <= 3
    assert solutions(f, x) == [(2,), (3,)]


def test_int_var_constant():
    f = CNF()
    x = f.new_int_var(range(4, 5))
    assert (x.min(), x.max(), x.card()) == (4, 4, 1)
    f += x + f.new_int_var(range(0, 2)) <= 4
    assert x.value(Assignment(set())) == 4, "a constant needs no literal to be read"


def test_int_var_unsatisfiable():
    f = CNF()
    x = f.new_int_var(range(0, 4))
    with pytest.raises(pindakaas.Unsatisfiable):
        f += x >= 9


@pytest.mark.parametrize(
    "build",
    [
        lambda f: f.int_var_from_order_literals([0, 1, 3], f.new_vars(1)),
        lambda f: f.int_var_from_order_literals([0, 1, 3], f.new_vars(3)),
        lambda f: f.int_var_from_direct_literals([0, 1, 3], f.new_vars(2)),
        lambda f: f.int_var_from_binary_literals([0, 1, 3], f.new_vars(1)),
        lambda f: f.int_var_from_binary_literals([0, 1, 3], f.new_vars(3)),
        lambda f: f.int_var_from_binary_literals([2, 3], f.new_vars(1), counts_from=3),
        lambda f: f.int_var_from_order_literals([], []),
    ],
)
def test_int_var_from_the_wrong_literals(build):
    with pytest.raises(ValueError):
        build(CNF())
