from abc import ABC, abstractmethod
from typing import Iterable, Optional, TypeAlias

from .pindakaas import CNFInner, Formula, Lit, WCNFInner, Encoder

Constraint: TypeAlias = Formula


class ClauseDatabase(ABC):
    def __iadd__(self, constraint: Constraint):
        self.add_encoding(constraint, None, [])
        return self

    @abstractmethod
    def add_clause(self, clause: Iterable[Lit]): ...

    @abstractmethod
    def add_encoding(
        self,
        constraint: Constraint,
        encoder: Optional[Encoder] = None,
        conditions: Optional[Iterable[Lit]] = [],
    ): ...

    def new_var(self):
        return self.new_vars(1).__iter__().__next__()

    @abstractmethod
    def new_vars(self, num: int) -> Iterable[Lit]: ...


class CNF(ClauseDatabase):
    _inner: CNFInner

    def __init__(self):
        self._inner = CNFInner()

    def add_clause(self, clause: Iterable[Lit]):
        return self._inner.add_clause(iter(clause))

    def add_encoding(
        self,
        constraint: Constraint,
        encoder: Optional[Encoder] = None,
        conditions: Optional[Iterable[Lit]] = [],
    ):
        return self._inner.add_encoding(constraint, encoder, conditions)

    def new_vars(self, num: int) -> Iterable[Lit]:
        return self._inner.new_vars(num)

    def to_dimacs(self) -> str:
        return self._inner.to_dimacs()


class WCNF(CNF):
    _inner: WCNFInner

    def __init__(self):
        self._inner = WCNFInner()

    def add_weighted_clause(self, clause: Iterable[Lit], weight: int):
        return self._inner.add_weighted_clause(iter(clause), weight)
