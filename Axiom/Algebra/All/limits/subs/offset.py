from util import *


@apply
def apply(self, index=0, offset=None):
    from Axiom.Algebra.Sum.limits.subs.offset import limits_subs
    return limits_subs(All, self, index, offset, simplify=False)


@prove
def prove(Eq):
    from Axiom import Algebra

    n, m, d = Symbol(integer=True)
    f = Function(integer=True)
    Eq << apply(All[n:1:m + 1](f(n) > 0), d)

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.apply(Algebra.All.to.All.limits.subs.offset, d)

    Eq << Eq[-1].this.rhs.apply(Algebra.All.of.All.limits.subs.offset, d)


if __name__ == '__main__':
    run()
# created on 2018-12-20
