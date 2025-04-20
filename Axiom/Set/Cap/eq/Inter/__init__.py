from util import *


@apply
def apply(self):
    fx, *limits = self.of(Cap)
    args = fx.of(Intersection)

    return Equal(self, Intersection(*(Cap(arg, *limits) for arg in args)))


@prove
def prove(Eq):
    from Axiom import Set, Algebra

    A, B = Symbol(etype=dtype.integer)
    x, y = Symbol(integer=True)
    f, g = Function(etype=dtype.real)
    Eq << apply(Cap[x:A, y:B](f(x, y) & g(x, y)))

    Eq << Set.Eq.given.And.Imp.apply(Eq[0], wrt=y)

    Eq <<= Eq[-2].this.rhs.apply(Set.Mem_Inter.given.And.Mem, simplify=False), \
    Eq[-1].this.lhs.apply(Set.And.Mem.of.Mem_Inter, simplify=False)

    Eq <<= Eq[-2].this.rhs.args[0].apply(Set.Mem_Cap.given.All_Mem), \
    Eq[-1].this.lhs.args[0].apply(Set.All_Mem.of.Mem_Cap)

    Eq <<= Eq[-2].this.rhs.args[0].apply(Set.Mem_Cap.given.All_Mem), \
    Eq[-1].this.lhs.args[0].apply(Set.All_Mem.of.Mem_Cap)

    Eq <<= Eq[-2].this.rhs.apply(Algebra.All.All.given.All.And), \
    Eq[-1].this.lhs.apply(Algebra.All.And.of.All.All)

    Eq <<= Eq[-2].this.lhs.apply(Set.All_Mem.of.Mem_Cap), \
    Eq[-1].this.rhs.apply(Set.Mem_Cap.given.All_Mem)


if __name__ == '__main__':
    run()


# created on 2021-01-31
from . import doit
from . import single_variable
from . import split
