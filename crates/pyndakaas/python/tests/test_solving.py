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


def test_assumptions():
    slv = pindakaas.solver.CaDiCaL()
    x, y = slv.new_vars(2)
    slv += x ^ y
    with slv.solve(assumptions=[x]) as result:
        assert result.status == pindakaas.solver.Status.SATISFIED
        assert result.value(x) is True
        assert result.value(y) is False
    with slv.solve(assumptions=[y]) as result:
        assert result.status == pindakaas.solver.Status.SATISFIED
        assert result.value(x) is False
        assert result.value(y) is True
    with slv.solve(assumptions=[x, y]) as result:
        assert result.status == pindakaas.solver.Status.UNSATISFIABLE
        assert result.failed(x) or result.failed(y), (
            "One or the other variable should have been used to prove UNSAT"
        )


def test_kissat():
    slv = pindakaas.solver.Kissat()
    x, y = slv.new_vars(2)
    slv.add_clause([x, y])
    slv.add_clause([~x, ~y])
    with slv.solve() as result:
        assert result.status == pindakaas.solver.Status.SATISFIED
        vx, vy = result.value(x), result.value(y)
        assert vx is not None
        assert vy is not None
        assert vx != vy
