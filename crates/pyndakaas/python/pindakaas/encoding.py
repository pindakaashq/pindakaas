from abc import ABC, abstractmethod
from typing import Iterable, Optional, TypeAlias

from .pindakaas import CNFInner, Encoder, Formula, Lit, WCNFInner

Constraint: TypeAlias = Formula


class ClauseDatabase(ABC):
    """The abstract class to represent objects (e.g. CNF, SAT solver) to which we can
    add clauses.
    """

    def __iadd__(self, constraint: Constraint):
        self.add_encoding(constraint)
        return self

    @abstractmethod
    def add_clause(self, clause: Iterable[Lit]):
        """Add a clause to the database.

        :param clause: An iterable of literals representing the clause to add
        :raises Unsatisfiable: If the formula has become unsatisfiable
        """
        ...

    @abstractmethod
    def add_encoding(
        self,
        constraint: Constraint,
        encoder: Optional[Encoder] = None,
        conditions: Optional[Iterable[Lit]] = None,
    ):
        """Add an encoding of a `constraint` to the database. Optionally, the constraint
        is implied by the given `conditions` (i.e. every clause is extended by the
        `conditions`), and the given `encoder` is used for the encoding.

        :param constraint: The constraint or formula to encode and add to the database
        :raises Unsatisfiable: If the formula has become unsatisfiable
        """
        ...

    def new_var(self):
        """Add a new variable to the database."""
        return self.new_vars(1).__iter__().__next__()

    @abstractmethod
    def new_vars(self, n: int) -> Iterable[Lit]:
        """Add `n` new variables to the database.

        :param n: The number of new variables
        :return: The new variables returned as literals
        """
        ...


class CNF(ClauseDatabase):
    """A representation for Boolean formulas in conjunctive normal form."""

    _inner: CNFInner

    def __init__(self):
        self._inner = CNFInner()

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

    def new_vars(self, n: int) -> Iterable[Lit]:
        return self._inner.new_vars(n)

    def to_dimacs(self) -> str:
        """Return a textual representation in the DIMACS format.

        :return: The CNF as a DIMACS string
        """
        return self._inner.to_dimacs()


class WCNF(CNF):
    """A representation for Boolean formulas in conjunctive normal form with weighted
    (soft) clauses.
    """

    _inner: WCNFInner

    def __init__(self):
        self._inner = WCNFInner()

    def add_weighted_clause(self, clause: Iterable[Lit], weight: int):
        """Add a weighted clause to the database.

        :param clause: An iterable of literals representing the clause to add
        :param weight: the weight of the clause
        """
        return self._inner.add_weighted_clause(iter(clause), weight)
