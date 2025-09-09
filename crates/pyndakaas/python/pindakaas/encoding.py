from abc import ABC, abstractmethod
from typing import Iterable, Optional

from .pindakaas import (
    CNFInner,
    Encoder,
    Formula,
    Lit,
    VarRange,
    WCNFInner,
    _wrap_encode_constraint,
)

Constraint = Formula


class ClauseDatabase(ABC):
    """The abstract class to represent objects to which we can add clauses.

    Examples of such classes include `CNF`, `WCNF`, and the various `Solver`
        implementations.
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

    def add_encoding(
        self,
        constraint: Constraint,
        encoder: Optional[Encoder] = None,
        conditions: Optional[Iterable[Lit]] = None,
    ):
        """Add an encoding of a `constraint` to the database.

        Optionally, the constraint is implied by the given `conditions` (i.e. every
            clause is extended by the `conditions`), and the given `encoder` is used
            for the encoding.

        :param constraint: The constraint or formula to encode and add to the database
        :raises Unsatisfiable: If the formula has become unsatisfiable
        """
        _wrap_encode_constraint(self, constraint, encoder, conditions)

    def new_var(self):
        """Add a new variable to the database."""
        r = self.new_var_range(1)
        assert r.start() == r.end()
        return r.start()

    def new_vars(self, n: int) -> Iterable[Lit]:
        """Add `n` new variables to the database.

        :param n: The number of new variables
        :return: The new variables returned as literals
        """
        return self.new_var_range(n)

    @abstractmethod
    def new_var_range(self, n: int) -> VarRange:
        """Add a continuous range of `n` new variables to the database.

        :param n: The number of new variables
        :return: The start and end of the range of the new variables (inclusive), given
            as literals.
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

    def clauses(self) -> Iterable[list[Lit]]:
        """Returns an iterator of the clauses currently included in the CNF.

        :return: An iterable of lists of literals representing the clauses.
        """
        return self._inner.clauses()

    def new_var_range(self, n: int) -> VarRange:
        return self._inner.new_var_range(n)

    def to_dimacs(self) -> str:
        """Return a textual representation in the DIMACS format.

        :return: The CNF as a DIMACS string
        """
        return self._inner.to_dimacs()

    def variables(self) -> Iterable[Lit]:
        """Returns an iterator of the variables currently included in the CNF.

        :return: An iterable of literals representing the variables.
        """
        return self._inner.variables()


class WCNF(CNF):
    """A representation for conjunctive normal form with weighted clauses.

    Note that `WCNF.clauses` only iterates over the hard clauses. Use
    `WCNF.weighted_clauses` to iterate over all clauses.
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

    def weighted_clauses(self) -> Iterable[tuple[Optional[int], list[Lit]]]:
        """Returns an iterator of the weighted clauses currently included in the WCNF.

        :return: An iterable of lists of literals representing the clauses.
        """
        return self._inner.weighted_clauses()
