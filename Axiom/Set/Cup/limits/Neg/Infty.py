from util import *


@apply
def apply(self):
    expr, (i,) = self.of(Cup)
    return Equal(self, Cup[i](expr._subs(i, -i)), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Set, Algebra

    i = Symbol(integer=True)
    f = Function(etype=dtype.real)
    Eq << apply(Cup[i](f(i)))

    Eq << Set.Eq.given.And.Imp.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(Set.Any_Mem.of.Mem_Cup), Eq[-1].this.rhs.apply(Set.Mem_Cup.given.Any_Mem)

    Eq <<= Eq[-2].this.rhs.apply(Set.Mem_Cup.given.Any_Mem), Eq[-1].this.lhs.apply(Set.Any_Mem.of.Mem_Cup)

    Eq <<= Eq[-2].this.lhs.apply(Algebra.Any.of.Any.limits.Neg.Infty)

    Eq <<= Eq[-1].this.lhs.apply(Algebra.Any.of.Any.limits.Neg.Infty)


if __name__ == '__main__':
    run()
# created on 2018-10-05
