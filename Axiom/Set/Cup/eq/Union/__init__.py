from util import *

@apply
def apply(self):
    fx, *limits = self.of(Cup)
    args = fx.of(Union)

    return Equal(self, Union(*(Cup(arg, *limits) for arg in args)))


@prove
def prove(Eq):
    from Axiom import Set, Algebra

    A, B = Symbol(etype=dtype.integer)
    x, y = Symbol(integer=True)
    f, g = Function(etype=dtype.real)
    Eq << apply(Cup[x:A, y:B](f(x, y) | g(x, y)))

    # Eq << apply(Cup[x:A](f(x) | g(x)))
    Eq << Set.Eq.given.And.Imp.apply(Eq[0], wrt=y)

    Eq <<= Eq[-2].this.rhs.apply(Set.Mem_Union.given.OrMemS, simplify=False), \
    Eq[-1].this.lhs.apply(Set.Or.of.Mem_Union, simplify=False)

    Eq <<= Eq[-2].this.rhs.args[0].apply(Set.Mem_Cup.given.Any_Mem), \
    Eq[-1].this.lhs.args[0].apply(Set.Any_Mem.of.Mem_Cup)

    Eq <<= Eq[-2].this.rhs.args[0].apply(Set.Mem_Cup.given.Any_Mem), \
    Eq[-1].this.lhs.args[0].apply(Set.Any_Mem.of.Mem_Cup)

    Eq <<= Eq[-2].this.rhs.apply(Algebra.Or.given.Any.Or), \
    Eq[-1].this.lhs.apply(Algebra.Any.Or.of.Or)

    Eq <<= Eq[-2].this.rhs.expr.apply(Set.Or.given.Mem), \
    Eq[-1].this.lhs.expr.apply(Set.Mem.of.Or)

    Eq <<= Eq[-2].this.lhs.apply(Set.Any_Mem.of.Mem_Cup), \
    Eq[-1].this.rhs.apply(Set.Mem_Cup.given.Any_Mem)


if __name__ == '__main__':
    run()

# created on 2021-02-10

from . import single_variable
from . import doit
from . import split
