"""
This module contains the machinery handling assumptions.

All symbolic objects have assumption attributes that can be accessed via
.is_<assumption name> attribute.

Assumptions determine certain properties of symbolic objects and can
have 3 possible values: True, False, None.  True is returned if the
object has the property and False is returned if it doesn't or can't
(i.e. doesn't make sense):

    >>> from sympy import I
    >>> I.is_algebraic
    True
    >>> I.is_real
    False
    >>> I.is_prime
    False

When the property cannot be determined (or when a method is not
implemented) None will be returned, e.g. a generic symbol, x, may or
may not be positive so a value of None is returned for x.is_positive.

By default, all symbolic values are in the largest set in the given context
without specifying the property. For example, a symbol that has a property
being integer, is also real, complex, etc.

Here follows a list of possible assumption names:

.. glossary::

    complex
        object can have only values from the set
        of complex numbers.

    imaginary
        object value is a number that can be written as a real
        number multiplied by the imaginary unit ``I``.  See
        [3]_.  Please note, that ``0`` is not considered to be an
        imaginary number, see
        `issue #7649 <https://github.com/sympy/sympy/issues/7649>`_.

    real
        object can have only values from the set
        of real numbers.

    integer
        object can have only values from the set
        of integers.

    odd
    even
        object can have only values from the set of
        odd (even) integers [2]_.

    prime
        object is a natural number greater than ``1`` that has
        no positive divisors other than ``1`` and itself.  See [6]_.

    composite
        object is a positive integer that has at least one positive
        divisor other than ``1`` or the number itself.  See [4]_.

    zero
        object has the value of ``0``.

    nonzero
        object is a complex number that is not zero.

    rational
        object can have only values from the set
        of rationals.

    algebraic
        object can have only values from the set
        of algebraic numbers [11]_.

    transcendental
        object can have only values from the set
        of transcendental numbers [10]_.

    irrational
        object value cannot be represented exactly by Rational, see [5]_.

    finite
    infinite
        object absolute value is bounded (arbitrarily large).
        See [7]_, [8]_, [9]_.

    negative
    nonnegative
        object can have only negative (nonnegative)
        values [1]_.

    positive
    nonpositive
        object can have only positive (only
        nonpositive) values.

    hermitian
    antihermitian
        object belongs to the field of hermitian
        (antihermitian) operators.

Examples
========

    >>> from sympy import Symbol
    >>> x = Symbol('x', real=True); x
    x
    >>> x.is_real
    True
    >>> x.is_complex
    True

See Also
========

.. seealso::

    :py:class:`sympy.core.numbers.ImaginaryUnit`
    :py:class:`sympy.core.numbers.Zero`
    :py:class:`sympy.core.numbers.One`

Notes
=====

Assumption values are stored in obj._assumptions dictionary or
are returned by getter methods (with property decorators) or are
attributes of objects/classes.


References
==========

.. [1] https://en.wikipedia.org/wiki/Negative_number
.. [2] https://en.wikipedia.org/wiki/Parity_%28mathematics%29
.. [3] https://en.wikipedia.org/wiki/Imaginary_number
.. [4] https://en.wikipedia.org/wiki/Composite_number
.. [5] https://en.wikipedia.org/wiki/Irrational_number
.. [6] https://en.wikipedia.org/wiki/Prime_number
.. [7] https://en.wikipedia.org/wiki/Finite
.. [8] https://docs.python.org/3/library/math.html#math.isfinite
.. [9] http://docs.scipy.org/doc/numpy/reference/generated/numpy.isfinite.html
.. [10] https://en.wikipedia.org/wiki/Transcendental_number
.. [11] https://en.wikipedia.org/wiki/Algebraic_number

"""
from __future__ import print_function, division

from sympy.core.facts import FactRules, FactKB
from sympy.core.core import BasicMeta
from sympy.core.compatibility import integer_types

from random import shuffle

_assume_rules = FactRules([

    'integer        ->  rational',
    'rational       ->  real',
    'rational       ->  algebraic',
    'algebraic      ->  complex & finite',
    'transcendental ==  complex & !algebraic & finite',
    'real           ->  hermitian',
    'imaginary      ->  complex & finite',
    'imaginary      ->  antihermitian',
    'extended_real  ->  commutative',
    'complex        ->  commutative',
    'complex        ->  infinite | finite',

    'odd            ==  integer & !even',
    'even           ==  integer & !odd',

    'extended_real  ->  complex',
    'extended_real  ->  real | infinite',
    'real           ==  extended_real & finite',

    'extended_real        ==  extended_negative | zero | extended_positive',
    'extended_negative    ==  extended_nonpositive & extended_nonzero',
    'extended_positive    ==  extended_nonnegative & extended_nonzero',

    'extended_nonpositive ==  extended_real & !extended_positive',
    'extended_nonnegative ==  extended_real & !extended_negative',

    'real           ==  negative | zero | positive',
    'negative       ==  nonpositive & nonzero',
    'positive       ==  nonnegative & nonzero',

    'nonpositive    ==  real & !positive',
    'nonnegative    ==  real & !negative',

    'positive       ==  extended_positive & finite',
    'negative       ==  extended_negative & finite',
    'nonpositive    ==  extended_nonpositive & finite',
    'nonnegative    ==  extended_nonnegative & finite',
    'nonzero        ->  extended_nonzero & finite',

    'zero           ->  even & finite',
    'zero           ==  extended_nonnegative & extended_nonpositive',
    'zero           ==  nonnegative & nonpositive',
    'nonzero        ->  complex',

    'prime          ->  integer & positive',
    'composite      ->  integer & positive & !prime',
    '!composite     ->  !positive | !even | prime',

    'irrational     ==  real & !rational',

    'imaginary      ->  !extended_real',

    'infinite       ->  !finite',
    'noninteger     ==  extended_real & !integer',
    'extended_nonzero == extended_real & !zero',
    'invertible == !singular',
    'random -> finite',
])

_assume_defined = _assume_rules.defined_facts.copy()
_assume_defined.add('polar')
_assume_defined = frozenset(_assume_defined)


def assumptions(expr, _check=None):
    """return the T/F assumptions of ``expr``"""
    n = sympify(expr)
    if n.is_Symbol:
        rv = n.assumptions0  # are any important ones missing?
        if _check is not None:
            rv = {k: rv[k] for k in set(rv) & set(_check)}
        return rv
    rv = {}
    for k in _assume_defined if _check is None else _check:
        v = getattr(n, 'is_{}'.format(k))
        if v is not None:
            rv[k] = v
    return rv


def common_assumptions(exprs, check=None):
    """return those assumptions which have the same True or False
    value for all the given expressions.

    Examples
    ========

    >>> from sympy.core.assumptions import common_assumptions
    >>> from sympy import oo, pi, sqrt
    >>> common_assumptions([-4, 0, sqrt(2), 2, pi, oo])
    {'commutative': True, 'composite': False,
    'extended_real': True, 'imaginary': False, 'odd': False}

    By default, all assumptions are tested; pass an iterable of the
    assumptions to limit those that are reported:

    >>> common_assumptions([0, 1, 2], ['positive', 'integer'])
    {'integer': True}
    """
    check = _assume_defined if check is None else set(check)
    if not check or not exprs:
        return {}

    # get all assumptions for each
    assume = [assumptions(i, _check=check) for i in sympify(exprs)]
    # focus on those of interest that are True
    for i, e in enumerate(assume):
        assume[i] = {k: e[k] for k in set(e) & check}
    # what assumptions are in common?
    common = set.intersection(*[set(i) for i in assume])
    # which ones hold the same value
    a = assume[0]
    return {k: a[k] for k in common if all(a[k] == b[k]
        for b in assume)}


def failing_assumptions(expr, **assumptions):
    """
    Return a dictionary containing assumptions with values not
    matching those of the passed assumptions.

    Examples
    ========

    >>> from sympy import failing_assumptions, Symbol

    >>> x = Symbol('x', real=True, positive=True)
    >>> y = Symbol('y')
    >>> failing_assumptions(6*x + y, real=True, positive=True)
    {'positive': None, 'real': None}

    >>> failing_assumptions(x**2 - 1, positive=True)
    {'positive': None}

    If *expr* satisfies all of the assumptions, an empty dictionary is returned.

    >>> failing_assumptions(x**2, positive=True)
    {}

    """
    expr = sympify(expr)
    failed = {}
    for k in assumptions:
        test = getattr(expr, 'is_%s' % k, None)
        if test is not assumptions[k]:
            failed[k] = test
    return failed  # {} or {assumption: value != desired}


def check_assumptions(expr, against=None, **assume):
    """
    Checks whether assumptions of ``expr`` match the T/F assumptions
    given (or possessed by ``against``). True is returned if all
    assumptions match; False is returned if there is a mismatch and
    the assumption in ``expr`` is not None; else None is returned.

    Explanation
    ===========

    *assume* is a dict of assumptions with True or False values

    Examples
    ========

    >>> from sympy import Symbol, pi, I, exp, check_assumptions
    >>> check_assumptions(-5, integer=True)
    True
    >>> check_assumptions(pi, real=True, integer=False)
    True
    >>> check_assumptions(pi, real=True, negative=True)
    False
    >>> check_assumptions(exp(I*pi/7), real=False)
    True
    >>> x = Symbol('x', real=True, positive=True)
    >>> check_assumptions(2*x + 1, real=True, positive=True)
    True
    >>> check_assumptions(-2*x - 5, real=True, positive=True)
    False

    To check assumptions of *expr* against another variable or expression,
    pass the expression or variable as ``against``.

    >>> check_assumptions(2*x + 1, x)
    True

    ``None`` is returned if ``check_assumptions()`` could not conclude.

    >>> check_assumptions(2*x - 1, x)

    >>> z = Symbol('z')
    >>> check_assumptions(z, real=True)

    See Also
    ========

    failing_assumptions

    """
    expr = sympify(expr)
    if against:
        if against is not None and assume:
            raise ValueError(
                'Expecting `against` or `assume`, not both.')
        assume = assumptions(against)
    known = True
    for k, v in assume.items():
        if v is None:
            continue
        e = getattr(expr, 'is_' + k, None)
        if e is None:
            known = None
        elif v != e:
            return False
    return known


class StdFactKB(FactKB):
    """A FactKB specialised for the built-in rules

    This is the only kind of FactKB that Basic objects should use.
    """

    def __init__(self, facts=None):
        super(StdFactKB, self).__init__(_assume_rules)
        # save a copy of the facts dict
        if not facts:
            self._generator = {}
        elif not isinstance(facts, FactKB):
            self._generator = facts.copy()
        else:
            self._generator = facts.generator
        if facts:
            self.deduce_all_facts(facts)

    def copy(self):
        return self.__class__(self)

    @property
    def generator(self):
        return self._generator.copy()


def as_property(fact):
    """Convert a fact name to the name of the corresponding property"""
    return 'is_%s' % fact


def make_property(fact):
    """Create the automagic property corresponding to a fact."""

    def _getit(self):
        try:
            return self._assumptions[fact]
        except KeyError:
            if self._assumptions is self.default_assumptions:
                self._assumptions = self.default_assumptions.copy()
            return self._ask(fact)

    _getit.func_name = as_property(fact)
    return property(_getit)


def _ask(fact, obj):
    """
    Find the truth value for a property of an object.

    This function is called when a request is made to see what a fact
    value is.

    For this we use several techniques:

    First, the fact-evaluation function is tried, if it exists (for
    example _eval_is_integer). Then we try related facts. For example

        rational   -->   integer

    another example is joined rule:

        integer & !odd  --> even

    so in the latter case if we are looking at what 'even' value is,
    'integer' and 'odd' facts will be asked.

    In all cases, when we settle on some fact value, its implications are
    deduced, and the result is cached in ._assumptions.
    """
    assumptions = obj._assumptions
    handler_map = obj._prop_handler

    # Store None into the assumptions so that recursive attempts at
    # evaluating the same fact don't trigger infinite recursion.
    assumptions._tell(fact, None)

    # First try the assumption evaluation function if it exists
    try:
        evaluate = handler_map[fact]
    except KeyError:
        pass
    else:
        a = evaluate(obj)
        if a is not None:
#             assumptions.deduce_all_facts(((fact, a),))
            assumptions[fact] = a
            return a

    # Try assumption's prerequisites
    prereq = list(_assume_rules.prereq[fact])
    shuffle(prereq)
    for pk in prereq:
        if pk in assumptions:
            continue
        if pk in handler_map:
            _ask(pk, obj)

            # we might have found the value of fact
            ret_val = assumptions.get(fact)
            if ret_val is not None:
                return ret_val

    # Note: the result has already been cached
    return None


class ManagedProperties(BasicMeta):
    """Metaclass for classes with old-style assumptions"""

    def __init__(self, *args, **kws):
        BasicMeta.__init__(self, *args, **kws)

        local_defs = {}
        for k in _assume_defined:
            attrname = as_property(k)
            v = self.__dict__.get(attrname, '')
            if isinstance(v, (bool, integer_types, type(None))):
                if v is not None:
                    v = bool(v)
                local_defs[k] = v

        defs = {}
        for base in reversed(self.__bases__):
            assumptions = getattr(base, '_explicit_class_assumptions', None)
            if assumptions is not None:
                defs.update(assumptions)
        defs.update(local_defs)

        self._explicit_class_assumptions = defs
        self.default_assumptions = StdFactKB(defs)

        self._prop_handler = {}
        for k in _assume_defined:
            eval_is_meth = getattr(self, '_eval_is_%s' % k, None)
            if eval_is_meth is not None:
                self._prop_handler[k] = eval_is_meth

        # Put definite results directly into the class dict, for speed
        for k, v in self.default_assumptions.items():
            setattr(self, as_property(k), v)

        # protection e.g. for Integer.is_even=F <- (Rational.is_integer=F)
        derived_from_bases = set()
        for base in self.__bases__:
            default_assumptions = getattr(base, 'default_assumptions', None)
            # is an assumption-aware class
            if default_assumptions is not None:
                derived_from_bases.update(default_assumptions)

        for fact in derived_from_bases - set(self.default_assumptions):
            pname = as_property(fact)
            if pname not in self.__dict__:
                setattr(self, pname, make_property(fact))

        # add any missing automagic property (e.g. for Basic)
        for fact in _assume_defined:
            pname = as_property(fact)
            if not hasattr(self, pname):
                setattr(self, pname, make_property(fact))
                
        # Finally, add class name property for Basic and self, eg, Basic.is_CLASSNAME = None, and CLASSNAME.is_CLASSNAME = True
        pname = as_property(self.__name__)
        if pname not in self.__dict__: 
            setattr(self, pname, True)
        
#         look in Method Resolution Order
        for base in reversed(self.__mro__):
            if not isinstance(base, ManagedProperties):
                continue
        
            assert base.__name__ == 'Basic', "self = %s, base = %s" % (self, base)
            if pname not in base.__dict__:
                setattr(base, pname, False)
            break
        
    def __getitem__(self, limits):
        from sympy.core.symbol import dtype
        if isinstance(limits, tuple):
            limits = [*limits]
            for i, limit in enumerate(limits):
                if isinstance(limit, slice):                    
                    x, a, b = limit.start, limit.stop, limit.step
                    if b is not None:
                        limits[i] = (x, a, b)
                    elif isinstance(a, int) or a.dtype in dtype.integer:
                        limits[i] = (x, 0, a - 1)
                    else:
                        limits[i] = (x, a)
                else:
                    limits[i] = limit
        elif isinstance(limits, slice):
            x, a, b = limits.start, limits.stop, limits.step
            if limits.step is not None:
                limits = [(x, a, b)]
            elif isinstance(a, int) or a.dtype in dtype.integer or a.is_Infinity:
                limits = [(x, 0, a - 1)]
            else:
                limits = [(x, a)]
        else:
            limits = [(limits,)]            
                    
        def operator(*args, **kwargs):
            return self(*args, *limits, **kwargs)

        return operator

    def __iter__(self):
        raise TypeError
