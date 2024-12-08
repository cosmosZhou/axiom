from util import *


@apply
def apply(self):
    fx, *limits = self.of(Cap)
    args = fx.of(Intersection)

    return Equal(self, Intersection(*(Cap(arg, *limits) for arg in args)))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    A, B = Symbol(etype=dtype.integer)
    x, y = Symbol(integer=True)
    f, g = Function(etype=dtype.real)
    Eq << apply(Cap[x:A, y:B](f(x, y) & g(x, y)))

    Eq << Sets.Eq.of.And.Imply.apply(Eq[0], wrt=y)

    Eq <<= Eq[-2].this.rhs.apply(Sets.In_Intersect.of.And.In, simplify=False), \
    Eq[-1].this.lhs.apply(Sets.In_Intersect.to.And.In, simplify=False)

    Eq <<= Eq[-2].this.rhs.args[0].apply(Sets.In_Cap.of.All_In), \
    Eq[-1].this.lhs.args[0].apply(Sets.In_Cap.to.All_In)

    Eq <<= Eq[-2].this.rhs.args[0].apply(Sets.In_Cap.of.All_In), \
    Eq[-1].this.lhs.args[0].apply(Sets.In_Cap.to.All_In)

    Eq <<= Eq[-2].this.rhs.apply(Algebra.All.All.of.All.And), \
    Eq[-1].this.lhs.apply(Algebra.All.All.to.All.And)

    Eq <<= Eq[-2].this.lhs.apply(Sets.In_Cap.to.All_In), \
    Eq[-1].this.rhs.apply(Sets.In_Cap.of.All_In)


if __name__ == '__main__':
    run()


# created on 2021-01-31
from . import single_variable
from . import doit
from . import st
from . import split
