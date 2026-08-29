from abc import ABC, abstractmethod
from typing import Iterable, Optional, Union

from .pindakaas import (
    CNFInner,
    Encoder,
    Formula,
    IntVar,
    Lit,
    VarRange,
    WCNFInner,
    _wrap_encode_constraint,
    _wrap_int_var_from_binary_literals,
    _wrap_int_var_from_direct_literals,
    _wrap_int_var_from_order_literals,
)

Constraint = Formula

Domain = Union[range, Iterable[int], Iterable[range]]
"""The values an integer variable can take.

Written as a :class:`range`, as the values themselves, or as several ranges::

    range(0, 4)          # 0, 1, 2, 3
    [0, 1, 3]            # 0, 1, 3
    [range(0, 2), range(3, 4)]  # the same three values

A :class:`range` is half open, as everywhere else in Python, so its `stop` is
    one past the greatest value. Giving the values themselves is the same as
    giving a range for each of them, so a domain of a million values is best
    written as ranges rather than listed.
"""


def _int_var_domain(domain: Domain) -> list:
    """`domain` as the inclusive, disjoint, ascending intervals Rust wants.

    :raises ValueError: If the domain has no values at all
    """
    if isinstance(domain, range):
        domain = [domain]
    intervals = []
    for part in domain:
        if isinstance(part, range):
            if part.step == 1:
                if part.start < part.stop:
                    intervals.append((part.start, part.stop - 1))
                continue
            part = list(part)
        else:
            part = [part]
        intervals.extend((v, v) for v in part)

    merged = []
    for start, end in sorted(intervals):
        # Touching counts as overlapping: `1..=2` and `3..=4` are `1..=4`.
        if merged and start <= merged[-1][1] + 1:
            merged[-1] = (merged[-1][0], max(merged[-1][1], end))
        else:
            merged.append((start, end))
    if not merged:
        raise ValueError("an integer variable needs at least one value")
    return merged


def _domain_card(intervals: list) -> int:
    """How many values the intervals hold together."""
    return sum(end - start + 1 for start, end in intervals)


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

    def new_int_var(self, domain: Domain) -> IntVar:
        """Create an integer variable over the values of `domain`.

        Nothing is encoded until the variable is used in a constraint, at which
            point it is given whichever Boolean encodings that constraint needs.

        :param domain: The values the variable can take, as a :data:`Domain`
        :return: The new integer variable
        :raises ValueError: If the domain has no values at all
        """
        return IntVar(_int_var_domain(domain))

    def int_var_from_order_literals(
        self, domain: Domain, literals: Iterable[Lit]
    ) -> IntVar:
        """Create an integer variable on literals that already exist.

        There is one literal per value beyond the least, and `literals[i]` must
            hold exactly when the variable has reached the `i + 1`'th value,
            which means each of them implying the one before.

        The literals are taken at their word: nothing is added to make them mean
            this. Where they do not, call :meth:`IntVar.constrain` on the result.

        :param domain: The values the variable can take, as a :data:`Domain`
        :param literals: The literal for reaching each value beyond the first
        :return: The new integer variable
        :raises ValueError: If there is not one literal per value beyond the first
        :raises Unsatisfiable: If the formula has become unsatisfiable
        """
        domain, literals = _int_var_domain(domain), list(literals)
        card = _domain_card(domain)
        if len(literals) != card - 1:
            raise ValueError(
                f"an order encoding of {card} values takes "
                f"{card - 1} literals, but {len(literals)} were given"
            )
        return _wrap_int_var_from_order_literals(self, domain, literals)

    def int_var_from_direct_literals(
        self, domain: Domain, literals: Iterable[Lit]
    ) -> IntVar:
        """Create an integer variable on literals that already exist.

        There is one literal per value, and `literals[i]` must hold exactly when
            the variable takes the `i`'th value, which means exactly one of them
            holding.

        The literals are taken at their word: nothing is added to make them mean
            this. Where they do not, call :meth:`IntVar.constrain` on the result.

        :param domain: The values the variable can take, as a :data:`Domain`
        :param literals: The literal for taking each value
        :return: The new integer variable
        :raises ValueError: If there is not one literal per value
        :raises Unsatisfiable: If the formula has become unsatisfiable
        """
        domain, literals = _int_var_domain(domain), list(literals)
        card = _domain_card(domain)
        if len(literals) != card:
            raise ValueError(
                f"a direct encoding of {card} values takes as many "
                f"literals, but {len(literals)} were given"
            )
        return _wrap_int_var_from_direct_literals(self, domain, literals)

    def int_var_from_binary_literals(
        self, domain: Domain, bits: Iterable[Lit], counts_from: int = 0
    ) -> IntVar:
        """Create an integer variable on bits that already exist.

        The bits are those of `value - counts_from`, least significant first, and
            must already stay within `domain`.

        The literals are taken at their word: nothing is added to make them mean
            this. Where they do not, call :meth:`IntVar.constrain` on the result.

        :param domain: The values the variable can take, as a :data:`Domain`
        :param bits: The bits of the variable, least significant first
        :param counts_from: What all the bits being zero stands for
        :return: The new integer variable
        :raises ValueError: If `counts_from` is above the least value, or there
            are not as many bits as reaching the greatest one takes
        :raises Unsatisfiable: If the formula has become unsatisfiable
        """
        domain, bits = _int_var_domain(domain), list(bits)
        least, greatest = domain[0][0], domain[-1][1]
        if counts_from > least:
            raise ValueError(f"bits counting from {counts_from} cannot reach {least}")
        needed = (greatest - counts_from).bit_length()
        if len(bits) != needed:
            raise ValueError(
                f"reaching {greatest} from {counts_from} takes {needed} bits, "
                f"but {len(bits)} were given"
            )
        return _wrap_int_var_from_binary_literals(self, domain, bits, counts_from)

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
