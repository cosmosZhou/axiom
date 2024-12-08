from util import *

@apply
def apply(self):
    fx, *limits = self.of(Cup)
    args = fx.of(Union)

    return Equal(self, Union(*(Cup(arg, *limits) for arg in args)))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    A, B = Symbol(etype=dtype.integer)
    x, y = Symbol(integer=True)
    f, g = Function(etype=dtype.real)
    Eq << apply(Cup[x:A, y:B](f(x, y) | g(x, y)))

    # Eq << apply(Cup[x:A](f(x) | g(x)))
    Eq << Sets.Eq.of.And.Imply.apply(Eq[0], wrt=y)

    Eq <<= Eq[-2].this.rhs.apply(Sets.In_Union.of.Or, simplify=False), \
    Eq[-1].this.lhs.apply(Sets.In_Union.to.Or, simplify=False)

    Eq <<= Eq[-2].this.rhs.args[0].apply(Sets.In_Cup.of.Any_In), \
    Eq[-1].this.lhs.args[0].apply(Sets.In_Cup.to.Any_In)

    Eq <<= Eq[-2].this.rhs.args[0].apply(Sets.In_Cup.of.Any_In), \
    Eq[-1].this.lhs.args[0].apply(Sets.In_Cup.to.Any_In)

    Eq <<= Eq[-2].this.rhs.apply(Algebra.Or.of.Any.Or), \
    Eq[-1].this.lhs.apply(Algebra.Or.to.Any.Or)

    Eq <<= Eq[-2].this.rhs.expr.apply(Sets.Or.of.In), \
    Eq[-1].this.lhs.expr.apply(Sets.Or.to.In)

    Eq <<= Eq[-2].this.lhs.apply(Sets.In_Cup.to.Any_In), \
    Eq[-1].this.rhs.apply(Sets.In_Cup.of.Any_In)


if __name__ == '__main__':
    run()

# created on 2021-02-10

from . import single_variable
from . import doit
from . import split
