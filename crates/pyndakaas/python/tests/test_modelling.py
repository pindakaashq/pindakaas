import pindakaas


def test_bool_lin():
    f = pindakaas.CNF()
    x, y, z = f.new_vars(3)
    assert str(x + 2) == "x₁ + 2", "__add__ incorrect"
    assert str(2 + x) == "x₁ + 2", "__radd__ incorrect"
    assert str(x - 2) == "x₁ + -2", "__sub__ incorrect"
    assert str(2 * x) == "2*x₁", "__mul__ incorrect"
    assert str(x * 2) == "2*x₁", "__rmul__ incorrect"
    assert str(x + y - z + 2) == "-x₃ + x₂ + x₁ + 2"
    c = sum([x, y, z])
    assert str(c) == "x₃ + x₂ + x₁"
    c *= 2
    assert str(c) == "2*x₃ + 2*x₂ + 2*x₁"
    c = x + y + z
    d = c == 2
    assert str(d) == "x₃ + x₂ + x₁ == 2"
    d = c < 2
    assert str(d) == "x₃ + x₂ + x₁ <= 1"
    d = c >= 2
    assert str(d) == "x₃ + x₂ + x₁ >= 2"


def test_bool_lin_ops():
    f = pindakaas.CNF()
    x, y, z = f.new_vars(3)
    f = x + y
    g = x - z
    assert str(f + 2) == "x₂ + x₁ + 2", "__add__ incorrect"
    assert str(2 + f) == "x₂ + x₁ + 2", "__radd__ incorrect"
    assert str(f + g) == "-x₃ + x₁ + x₂ + x₁", "__add__ incorrect"
    assert str(f * 2) == "2*x₂ + 2*x₁", "__mul__ incorrect"
    assert str(2 * f) == "2*x₂ + 2*x₁", "__rmul__ incorrect"


def test_formula_ops():
    f = pindakaas.CNF()
    x, y, z = f.new_vars(3)
    f = x & y
    g = x | z
    assert str(f & True) == "x₁ ∧ x₂ ∧ true", "__and__ incorrect"
    assert str(True & f) == "x₁ ∧ x₂ ∧ true", "__rand__ incorrect"
    assert str(f & g) == "x₁ ∧ x₂ ∧ (x₁ ∨ x₃)", "__and__ incorrect"
    assert str(f | True) == "(x₁ ∧ x₂) ∨ true", "__or__ incorrect"
    assert str(True | f) == "(x₁ ∧ x₂) ∨ true", "__ror__ incorrect"
    assert str(f | g) == "x₁ ∨ x₃ ∨ (x₁ ∧ x₂)", "__or__ incorrect"
    assert str(f ^ True) == "(x₁ ∧ x₂) ⊻ true", "__xor__ incorrect"
    assert str(True ^ f) == "(x₁ ∧ x₂) ⊻ true", "__rxor__ incorrect"
    assert str(f ^ g) == "(x₁ ∧ x₂) ⊻ (x₁ ∨ x₃)", "__xor__ incorrect"


def test_lit_ops():
    f = pindakaas.CNF()
    x, y = f.new_vars(2)
    assert str(x & True) == "x₁ ∧ true", "__and__ incorrect"
    assert str(True & x) == "x₁ ∧ true", "__rand__ incorrect"
    assert str(x | True) == "x₁ ∨ true", "__or__ incorrect"
    assert str(True | x) == "x₁ ∨ true", "__ror__ incorrect"
    assert str(x ^ True) == "x₁ ⊻ true", "__xor__ incorrect"
    assert str(True ^ x) == "x₁ ⊻ true", "__rxor__ incorrect"
    assert str(~x | ~y) == "¬x₁ ∨ ¬x₂"
    assert str(x & y) == "x₁ ∧ x₂"
    assert str(x ^ y) == "x₁ ⊻ x₂"
    assert str(x == y) == "x₁ ≡ x₂"
