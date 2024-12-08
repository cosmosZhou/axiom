from util import *


@apply
def apply(self, index=0, offset=None):
    from Axiom.Algebra.Sum.limits.subs.offset import limits_subs
    return Equal(self, limits_subs(Cap, self, index, offset), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    a, b, n, d = Symbol(integer=True)
    f = Function(etype=dtype.integer)
    Eq << apply(Cap[n:a:b](f(n)), d)

    Eq << Sets.Eq.of.And.Imply.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(Sets.In_Cap.to.All_In), Eq[-1].this.lhs.apply(Sets.In_Cap.to.All_In)

    Eq <<= Eq[-2].this.rhs.apply(Sets.In_Cap.of.All_In), Eq[-1].this.rhs.apply(Sets.In_Cap.of.All_In)

    Eq <<= Eq[-2].this.lhs.apply(Algebra.All.to.All.limits.subs.offset, d)

    Eq <<= Eq[-1].this.lhs.apply(Algebra.All.to.All.limits.subs.offset, -d)


if __name__ == '__main__':
    run()
# created on 2021-01-28
