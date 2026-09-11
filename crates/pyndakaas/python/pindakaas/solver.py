"""SAT solvers, models, and failed assumptions."""

from abc import ABC, abstractmethod
from contextlib import contextmanager
from datetime import timedelta
from typing import ContextManager, Iterable, Iterator, Optional

from .encoding import ClauseDatabase, Constraint
from .pindakaas import Encoder, Lit
from .pindakaas.solver import CaDiCaLInner, KissatInner, Status


class Result(ABC):
    """A solve result valid inside the ``solve()`` context manager.

    Access after leaving the context raises ``RuntimeError``.
    """

    @property
    @abstractmethod
    def status(self) -> Status:
        """Search status."""
        ...

    @abstractmethod
    def value(self, lit: Lit) -> Optional[bool]:
        """The literal's value in a satisfying model.

        Args:
            lit: Literal to inspect.

        Returns:
            Its truth value for a satisfied result, or ``None`` otherwise.
            Bundled backends report unassigned literals as ``False``.
        """
        ...

    @abstractmethod
    def failed(self, lit: Lit) -> Optional[bool]:
        """Membership in the failed-assumption core.

        For literals not assumed in this search, the Boolean result is unspecified.

        Args:
            lit: Assumption literal to inspect.

        Returns:
            Whether it belongs to the failed core, or ``None`` unless the
            result is unsatisfiable and the backend supports assumptions.
        """
        ...


class Solver(ClauseDatabase):
    """A clause database that can search for a satisfying assignment."""

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
        """Search the current clauses under temporary assumptions.

        The result is valid only inside the context. Adding clauses, allocating
        variables, or starting another solve on this solver during that context
        raises ``RuntimeError``.

        Args:
            assumptions: Literals required to hold for this search only.
            time_limit: Wall-clock limit, or no limit when omitted.

        Yields:
            The search result.

        Raises:
            NotImplementedError: The backend rejects time limits or assumptions.
            RuntimeError: A result already has exclusive access to this solver.
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
        """A fresh solver with no clauses."""
        self._inner = CaDiCaLInner()

    def _set_time_limit(self, limit: Optional[timedelta]):
        return self._inner.set_time_limit(limit)

    @contextmanager
    def _solve_assuming(self, assumptions: Iterable[Lit]) -> Iterator[Result]:
        with self._inner.solve_assuming(list(assumptions)) as result:
            yield result

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

    def _set_option(self, option: str, value: int):
        return self._inner._set_option(option, value)


class Kissat(Solver):
    """The `Kissat <https://github.com/arminbiere/kissat>`_ SAT solver.

    Nonempty assumptions raise ``NotImplementedError``.
    """

    _inner: KissatInner

    def __init__(self):
        self._inner = KissatInner()

    def _set_time_limit(self, limit: Optional[timedelta]):
        return self._inner.set_time_limit(limit)

    @contextmanager
    def _solve_assuming(self, assumptions: Iterable[Lit]) -> Iterator[Result]:
        with self._inner.solve_assuming(list(assumptions)) as result:
            yield result

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
