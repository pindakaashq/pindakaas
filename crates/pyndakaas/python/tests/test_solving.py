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


# def test_assumptions():
#     slv = pindakaas.solver.CaDiCaL()
#     # same as the tie/shirt example unit test in Cadical
#     x, y = slv.new_vars(2)
#     slv += x ^ y
#     slv.add_clause([~x, y])
#     with slv.solve(assumptions=[y]) as result:
#         assert result.status == pindakaas.solver.Status.SATISFIED
#         assert result.value(y) is True
#         assert result.value(x) is False
#     with slv.solve(assumptions=[x]) as result:
#         assert result.status == pindakaas.solver.Status.UNSATISFIABLE
#         assert result.failed(x) is True, "`x` should be responsible"
#         assert result.failed(y) is None, "`y` is not an assumption, so is not in the core"
