from __future__ import absolute_import, print_function, unicode_literals

from itertools import chain

from wolframclient.utils import six
from wolframclient.utils.encoding import force_text

__all__ = ["WLSymbol", "WLFunction", "WLSymbolFactory", "WLInputExpression"]


def sympify(expr, **kwargs):
    if isinstance(expr, int):
        return expr
    
    if isinstance(expr, tuple):        
        from sympy import Matrix
        if isinstance(expr[0], tuple):
            return Matrix(tuple(tuple(sympify(e, **kwargs) for e in t) for t in expr))
        else:
            return Matrix(tuple(sympify(e, **kwargs) for e in expr))
            
    return expr.sympify(**kwargs)


class WLExpressionMeta(object):
    """Abstract class to subclass when building representation of Wolfram Language expressions as Python object."""

    if six.PY2:

        def __nonzero__(self):
            return True

    def __bool__(self):
        return True

    def __call__(self, *args, **opts):
        return WLFunction(self, *args, **opts)


class WLSymbol(WLExpressionMeta):
    """Represent a Wolfram Language symbol in Python."""

    __slots__ = "name"

    def __init__(self, name):
        if isinstance(name, six.binary_type):
            self.name = force_text(name)
        elif isinstance(name, six.text_type):
            self.name = name
        else:
            raise ValueError(
                "Symbol name should be %s not %s. You provided: %s"
                % (six.text_type.__name__, name.__class__.__name__, name)
            )

    def __hash__(self):
        return hash((WLSymbol.__name__, self.name))

    def __len__(self):
        return 0  # consistent with Length(x)

    def __eq__(self, other):
        return isinstance(other, WLSymbol) and self.name == other.name

    def __repr__(self):
        return self.name

    def __str__(self):
        return self.name

    def sympify(self, *args, **global_variables):
        name = self.name
        if args:
            import sympy  # @UnusedImport
            return getattr(sympy, name)(*(sympify(arg, **global_variables) for arg in args))
        else:
            return global_variables[name]


class WLFunction(WLExpressionMeta):
    """Represent a Wolfram Language function with its head and arguments.
    """

    # reminder: use slots to reduce memory usage:
    # https://stackoverflow.com/questions/472000/usage-of-slots
    # https://www.codementor.io/satwikkansal/python-practices-for-efficient-code-performance-memory-and-usability-aze6oiq65

    __slots__ = "head", "args"

    def __init__(self, head, *args, **opts):
        self.head = head

        if opts:
            self.args = tuple(
                chain(args, (WLSymbol("Rule")(WLSymbol(k), v) for k, v in opts.items()))
            )
        else:
            self.args = args

    def __hash__(self):
        return hash((self.head, self.args))

    def __getitem__(self, i):
        return self.args.__getitem__(i)

    def __eq__(self, other):
        return (
            isinstance(other, WLFunction)
            and self.head == other.head
            and self.args == other.args
        )

    def __len__(self):
        return len(self.args)

    def __repr__(self):
        if len(self) > 4:
            return "%s[%s, << %i >>, %s]" % (
                repr(self.head),
                ", ".join(repr(x) for x in self.args[:2]),
                len(self) - 4,
                ", ".join(repr(x) for x in self.args[-2:]),
            )
        else:
            return "%s[%s]" % (repr(self.head), ", ".join(repr(x) for x in self.args))

    def sympify(self, **global_variables):
        return self.head.sympify(*self.args, **global_variables)


class WLSymbolFactory(WLSymbol):
    """Provide a convenient way to build objects representing arbitrary Wolfram Language expressions through the use of
    attributes.

    This class is conveniently instantiated at startup as :class:`~wolframclient.language.wl`,
    :class:`~wolframclient.language.Global`
    and :class:`~wolframclient.language.System`. It should be instantiated only to represent many symbols belonging to
    the same specific context.

    Example::

        >>> dev = WLSymbolFactory('Developer')
        >>> dev.PackedArrayQ
        Developer`PackedArrayQ
    
    Alternative::

        >>> wl.Developer.PackedArrayQ
        Developer`PackedArrayQ

    """

    def __init__(self, name=None):
        self.name = name

    def __getattr__(self, attr):
        # this operation is always creating a new immutable symbol factory
        return self.__class__(self.name and "%s`%s" % (self.name, attr) or attr)


class WLInputExpression(WLExpressionMeta):
    """ Represent a string input form expression. """

    def __init__(self, inputs):
        if isinstance(inputs, (six.binary_type, six.text_type)):
            self.input = inputs
        else:
            raise ValueError("input must be string or bytes")

    def __repr__(self):
        return self.input
#         return "(%s)" % self.input

    def __str__(self):
        return self.input
#         return "(%s)" % self.input
