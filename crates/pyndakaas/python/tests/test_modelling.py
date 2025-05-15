import pindakaas


def test_bool_lin():
    f = pindakaas.CNF()
    x, y, z = f.new_vars(3)
    c = x + y - z + 2
    assert str(c) == "-x₃ + x₂ + x₁ + 2"
    c = sum([y, y, z], x)
    assert str(c) == "x₃ + x₂ + x₂ + x₁"
    c *= 2
    assert str(c) == "2*x₃ + 2*x₂ + 2*x₂ + 2*x₁"
    c = x + y + z
    d = c == 2
    assert str(d) == "x₃ + x₂ + x₁ == 2"
    d = c < 2
    assert str(d) == "x₃ + x₂ + x₁ <= 1"
    d = c >= 2
    assert str(d) == "x₃ + x₂ + x₁ >= 2"


def test_lit_ops():
    f = pindakaas.CNF()
    x, y, z = f.new_vars(3)
    a = ~x | ~y
    assert str(a) == "¬x₁ ∨ ¬x₂"
    b = y & z
    assert str(b) == "x₂ ∧ x₃"
    c = x ^ y
    assert str(c) == "x₁ ⊻ x₂"
    d = x ^ True
    assert str(d) == "x₁ ⊻ true"
    e = x == y
    assert str(e) == "x₁ ≡ x₂"
