from abc import ABC, abstractmethod
from typing import Iterable, Optional, Union

from .pindakaas import (
    BoolVal,
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

Ranges avoid listing every value in a large domain.
"""


def _int_var_domain(domain: Domain) -> list:
    """`domain` as the inclusive, disjoint, ascending intervals Rust wants.

    Raises:
        ValueError: The domain has no values.
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
    """Destination for clauses and fresh variables emitted by an encoder.

    Implemented by ``CNF``, ``WCNF``, and the solver classes.
    """

    def __iadd__(self, constraint: Constraint):
        self.add_encoding(constraint)
        return self

    @abstractmethod
    def add_clause(self, clause: Iterable[Union[Lit, BoolVal, bool]]):
        """Adds a clause after folding constant Boolean values.

        Args:
            clause: Literals or constant Boolean values in the disjunction.

        Raises:
            Unsatisfiable: The reduced clause makes the database inconsistent.
        """
        ...

    def add_encoding(
        self,
        constraint: Constraint,
        encoder: Optional[Encoder] = None,
        conditions: Optional[Iterable[Lit]] = None,
    ):
        """Clauses encoding a constraint, optionally under conditions.

        Args:
            constraint: Formula or constraint to encode.
            encoder: Encoding algorithm, or its default when omitted.
            conditions: Literals whose conjunction implies the constraint.

        Raises:
            InvalidEncoder: The encoder does not accept this constraint type.
            Unsatisfiable: The encoding makes the database inconsistent.
        """
        _wrap_encode_constraint(self, constraint, encoder, conditions)

    def new_var(self):
        """Allocates one previously unused positive literal."""
        r = self.new_var_range(1)
        assert r.start() == r.end()
        return r.start()

    def new_vars(self, n: int) -> Iterable[Lit]:
        """Allocates a consecutive range of previously unused variables.

        Args:
            n: Number of variables.

        Returns:
            The variables as positive literals.
        """
        return self.new_var_range(n)

    def new_int_var(self, domain: Domain) -> IntVar:
        """Create an integer variable whose Boolean encoding is created on demand.

        Args:
            domain: Values the variable may take.

        Raises:
            ValueError: The domain has no values.
        """
        return IntVar(_int_var_domain(domain))

    def int_var_from_order_literals(
        self, domain: Domain, literals: Iterable[Lit]
    ) -> IntVar:
        """An integer variable on existing order literals.

        `literals[i]` must mean the variable reaches the (zero-based)
        `i + 1`-th value in the sorted domain.
        The implication chain is trusted; use :meth:`IntVar.constrain` to
        enforce it.

        Args:
            domain: Values the variable may take.
            literals: Literal for reaching each value beyond the first.

        Raises:
            ValueError: There is not one literal per value beyond the first.
            Unsatisfiable: Channelling to an existing view causes a contradiction.
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
        """An integer variable on existing direct literals.

        `literals[i]` must mean the variable takes the (zero-based)
        `i`-th value in the sorted domain.
        Exactly-one is trusted; use :meth:`IntVar.constrain` to enforce it.

        Args:
            domain: Values the variable may take.
            literals: Literal for taking each value.

        Raises:
            ValueError: There is not one literal per value.
            Unsatisfiable: Channelling to an existing view causes a contradiction.
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
        """An integer variable on existing binary literals.

        Bits represent `value - counts_from`, least significant first, and
        must already respect `domain`. Use :meth:`IntVar.constrain` to
        enforce it.

        Args:
            domain: Values the variable may take.
            bits: Value bits, least significant first.
            counts_from: Value represented by all bits being false.

        Raises:
            ValueError: The offset is above the least value or the bit count is wrong.
            Unsatisfiable: Channelling to an existing view causes a contradiction.
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
        """A consecutive range of previously unused variables.

        Args:
            n: Number of variables.

        Returns:
            Inclusive range represented by positive literals.
        """
        ...


class CNF(ClauseDatabase):
    """In-memory conjunctive normal form."""

    _inner: CNFInner

    def __init__(self):
        self._inner = CNFInner()

    def add_clause(self, clause: Iterable[Union[Lit, BoolVal, bool]]):
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
        """Stored clauses in insertion order.

        Returns:
            Copies of the clauses as lists of literals.
        """
        return self._inner.clauses()

    def new_var_range(self, n: int) -> VarRange:
        return self._inner.new_var_range(n)

    def to_dimacs(self) -> str:
        """DIMACS CNF serialization."""
        return self._inner.to_dimacs()

    def variables(self) -> Iterable[Lit]:
        """Allocated variables.

        Returns:
            Positive literals in allocation order.
        """
        return self._inner.variables()


class WCNF(CNF):
    """Conjunctive normal form with weighted clauses.

    `clauses` yields only hard clauses; `weighted_clauses` yields all clauses.
    """

    _inner: WCNFInner

    def __init__(self):
        self._inner = WCNFInner()

    def add_weighted_clause(self, clause: Iterable[Lit], weight: int):
        """Adds a soft clause with the given cost when violated.

        Args:
            clause: Literals in the disjunction.
            weight: Cost of violating the clause.

        Raises:
            Unsatisfiable: The reduced clause is empty.
        """
        return self._inner.add_weighted_clause(iter(clause), weight)

    def weighted_clauses(self) -> Iterable[tuple[Optional[int], list[Lit]]]:
        """Hard and soft clauses in insertion order.

        Returns:
            ``(weight, clause)`` pairs; a ``None`` weight marks a hard clause.
        """
        return self._inner.weighted_clauses()
