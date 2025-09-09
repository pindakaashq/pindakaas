"""A module containing solvers and solving related classes."""

from abc import ABC, abstractmethod
from contextlib import contextmanager
from datetime import timedelta
from typing import ContextManager, Iterable, Iterator, Optional

from .encoding import ClauseDatabase, Constraint
from .pindakaas import Encoder, Lit
from .pindakaas.solver import CaDiCaLInner, KissatInner, Status


class Result(ABC):
    """The Result object returned after calling `solve()`.

    It gives access to e.g. solver status and the values of variables.
    """

    @property
    @abstractmethod
    def status(self) -> Status:
        """Return result from solving the database."""
        ...

    @abstractmethod
    def value(self, lit: Lit) -> Optional[bool]:
        """Return value for literal `lit`, or `None` if `lit` is assigned.

        :param lit: the literal for which to return the value

        :return: the value of `lit` if assigned

        """
        ...

    @abstractmethod
    def failed(self, lit: Lit) -> Optional[bool]:
        """Check if the given assumption literal was used to prove the unsatisfiability.

        The unsatisfiability of the formula is under the assumptions used for the last
        SAT search. Note also that for literals `lit` which are not assumption literals,
        the behavior of is not specified.

        :param lit: the assumption literal for which to return whether it contributed to
            the unsatisfiable result

        :return: whether `lit` contributed to the unsatisfiable result
        """
        ...


class Solver(ClauseDatabase):
    """An abstract class which extends a `ClauseDatabase` with solving capabilities."""

    def _set_time_limit(self, limit: Optional[timedelta]):
        if limit is not None:
            raise NotImplementedError("Solver does not support setting a time limit")

    @abstractmethod
    def _solve_assuming(self, assumptions: Iterable[Lit]) -> ContextManager[Result]: ...

    @contextmanager
    def solve(
        self,
        assumptions: Optional[Iterable[Lit]] = None,
        time_limit: Optional[timedelta] = None,
    ) -> Iterator[Result]:
        """Solve the current `ClauseDatabase`.

        :param assumptions: an optional iterable of assumptions literals which must hold
            for this solve call
        :param time_limit: an optional time limit before which the solver is terminated
            and the result is Unknown
        """
        self._set_time_limit(time_limit)
        assumptions = assumptions if assumptions is not None else []
        try:
            with self._solve_assuming(assumptions) as result:
                yield result
        finally:
            self._set_time_limit(None)


class CaDiCaL(Solver):
    """The `CaDiCaL <https://github.com/arminbiere/cadical>`_ SAT solver."""

    _inner: CaDiCaLInner

    def __init__(self):
        """Initialize solver."""
        self._inner = CaDiCaLInner()

    def _set_time_limit(self, limit: Optional[timedelta]):
        return self._inner.set_time_limit(limit)

    @contextmanager
    def _solve_assuming(self, assumptions: Iterable[Lit]) -> Iterator[Result]:
        # TODO: Investigate whether it is possible to avoid copying the solution
        (status, mapping) = self._inner.solve_assuming(assumptions)
        yield MapResult(status, mapping)

    def add_clause(self, clause: Iterable[Lit]):
        return self._inner.add_clause(iter(clause))

    def add_encoding(
        self,
        constraint: Constraint,
        encoder: Optional[Encoder] = None,
        conditions: Optional[Iterable[Lit]] = None,
    ):
        conditions = list(conditions) if conditions is not None else []
        return self._inner.add_encoding(constraint, encoder, conditions)

    def new_var_range(self, n: int):
        return self._inner.new_var_range(n)


class Kissat(Solver):
    """The `Kissat <https://github.com/arminbiere/kissat>`_ SAT solver."""

    _inner: KissatInner

    def __init__(self):
        self._inner = KissatInner()

    def _set_time_limit(self, limit: Optional[timedelta]):
        return self._inner.set_time_limit(limit)

    @contextmanager
    def _solve_assuming(self, assumptions: Iterable[Lit]) -> Iterator[Result]:
        # TODO: Investigate whether it is possible to avoid copying the solution
        (status, mapping) = self._inner.solve_assuming(assumptions)
        yield MapResult(status, mapping)

    def add_clause(self, clause: Iterable[Lit]):
        return self._inner.add_clause(iter(clause))

    def add_encoding(
        self,
        constraint: Constraint,
        encoder: Optional[Encoder] = None,
        conditions: Optional[Iterable[Lit]] = None,
    ):
        conditions = list(conditions) if conditions is not None else []
        return self._inner.add_encoding(constraint, encoder, conditions)

    def new_var_range(self, n: int):
        return self._inner.new_var_range(n)


class MapResult(Result):
    def __init__(self, status: Status, mapping: dict[int, bool]):
        self._status = status
        self._mapping = mapping

    @property
    def status(self) -> Status:
        return self._status

    def value(self, lit: Lit) -> Optional[bool]:
        if self.status == Status.SATISFIED:
            return self._mapping.get(int(lit))
        return None

    def failed(self, lit: Lit) -> Optional[bool]:
        if self.status == Status.UNSATISFIABLE:
            return self._mapping.get(int(lit))
        return None
