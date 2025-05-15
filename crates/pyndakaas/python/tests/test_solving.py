import pindakaas


def test_cadical():
    slv = pindakaas.solver.CaDiCaL()
    x, y = slv.new_vars(2)
    slv.add_clause([x, y])
    slv.add_clause([~x, ~y])
    with slv.solve() as result:
        assert result.status == pindakaas.solver.Status.SATISFIED
        vx, vy = result.value(x), result.value(y)
        assert vx is not None
        assert vy is not None
        assert vx != vy
