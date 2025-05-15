from abc import ABC, abstractmethod
from contextlib import contextmanager
from typing import ContextManager, Iterable, Iterator, Optional
from datetime import timedelta

from .encoding import ClauseDatabase, Constraint
from .pindakaas import Lit, Encoder
from .pindakaas.solver import Status, CaDiCaLInner


class Result(ABC):
    @property
    @abstractmethod
    def status(self) -> Status: ...

    @abstractmethod
    def value(self, var: Lit) -> Optional[bool]: ...

    @abstractmethod
    def failed(self, var: Lit) -> Optional[bool]: ...


class Solver(ClauseDatabase):
    def _set_time_limit(self, limit: Optional[timedelta]):
        if limit is not None:
            raise NotImplementedError("Solver does not support setting a time limit")

    @abstractmethod
    def _solve_assuming(self, assumptions: Iterable[Lit]) -> ContextManager[Result]: ...

    @contextmanager
    def solve(
        self, assumptions: Optional[Iterable[Lit]] = None, time_limit: Optional[timedelta] = None
    ) -> Iterator[Result]:
        self._set_time_limit(time_limit)
        assumptions = assumptions if assumptions is not None else []
        try:
            with self._solve_assuming(assumptions) as result:
                yield result
        finally:
            self._set_time_limit(None)


class CaDiCaL(Solver):
    _inner: CaDiCaLInner

    def __init__(self):
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

    def add_encoding(self, constraint: Constraint, encoder: Optional[Encoder] = None):
        return self._inner.add_encoding(constraint, encoder)

    def new_vars(self, num: int):
        return self._inner.new_vars(num)


class MapResult(Result):
    def __init__(self, status: Status, mapping: dict[int, bool]):
        self._status = status
        self._mapping = mapping

    @property
    def status(self) -> Status:
        return self._status

    def value(self, var: Lit) -> Optional[bool]:
        if self.status == Status.SATISFIED:
            return self._mapping.get(int(var))
        return None

    def failed(self, var: Lit) -> Optional[bool]:
        if self.status == Status.UNSATISFIABLE:
            return self._mapping.get(int(var)) == 0
        return None
