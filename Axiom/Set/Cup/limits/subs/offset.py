from util import *


@apply
def apply(self, index=0, offset=None):
    from Axiom.Algebra.Sum.limits.subs.offset import limits_subs
    return Equal(self, limits_subs(Cup, self, index, offset), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Set, Algebra

    a, b, n, d = Symbol(integer=True)
    f = Function(etype=dtype.integer)
    Eq << apply(Cup[n:a:b](f(n)), d)

    Eq << Set.Eq.given.And.Imp.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(Set.Any_Mem.of.Mem_Cup), Eq[-1].this.lhs.apply(Set.Any_Mem.of.Mem_Cup)

    Eq <<= Eq[-2].this.rhs.apply(Set.Mem_Cup.given.Any_Mem), Eq[-1].this.rhs.apply(Set.Mem_Cup.given.Any_Mem)

    Eq <<= Eq[-2].this.lhs.apply(Algebra.Any.of.Any.limits.subs.offset, d)

    Eq <<= Eq[-1].this.lhs.apply(Algebra.Any.of.Any.limits.subs.offset, -d)


if __name__ == '__main__':
    run()
# created on 2018-10-06
