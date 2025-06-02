import pindakaas
import pytest


def test_unsat():
    f = pindakaas.CNF()
    with pytest.raises(pindakaas.Unsatisfiable):
        f.add_clause([])


def test_cnf():
    f = pindakaas.CNF()
    x, y = f.new_vars(2)
    f.add_clause([x, y])
    assert f.to_dimacs() == "p cnf 2 1\n1 2 0\n"


def test_encode_bool_lin_unsat():
    f = pindakaas.CNF()
    x, y, z = f.new_vars(3)
    with pytest.raises(pindakaas.Unsatisfiable):
        f += x * 3 + y * 2 + z >= 10


def test_invalid_encoder():
    f = pindakaas.CNF()
    x, y, z = f.new_vars(3)
    with pytest.raises(pindakaas.InvalidEncoder):
        f.add_encoding(x * 3 + y * 2 + z >= 3, encoder=pindakaas.Encoder.PAIRWISE)


def test_encode_bool_lin_default():
    f = pindakaas.CNF()
    x, y, z = f.new_vars(3)
    f += x * 3 + y * 2 + z >= 3
    x, y, z = f.new_vars(3)
    f.add_encoding(x + y + z == 1)
    print(f.to_dimacs())
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
    f = pindakaas.CNF()
    x, y, z = f.new_vars(3)
    f += x ^ z
    f.add_encoding(x == y, pindakaas.Encoder.TSEITIN)
    f.add_encoding(x & y)
    assert f.to_dimacs() == "p cnf 3 6\n1 3 0\n-1 -3 0\n-1 2 0\n1 -2 0\n1 0\n2 0\n"


def test_wcnf():
    f = pindakaas.WCNF()
    x, y = f.new_vars(2)
    f.add_clause([x, y])
    f.add_weighted_clause([x], 1)
    f.add_weighted_clause([y], 2)
    assert f.to_dimacs() == "p wcnf 2 3 4\n4 1 2 0\n1 1 0\n2 2 0\n"


def test_conditions():
    f = pindakaas.CNF()
    x, y, p = f.new_vars(3)
    f.add_encoding(x ^ y, conditions=[p])
    assert f.to_dimacs() == "p cnf 3 2\n3 1 2 0\n3 -1 -2 0\n"
