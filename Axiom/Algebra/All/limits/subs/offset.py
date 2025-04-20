from util import *


@apply
def apply(self, index=0, offset=None):
    from Axiom.Algebra.Sum.limits.subs.offset import limits_subs
    return limits_subs(All, self, index, offset, simplify=False)


@prove
def prove(Eq):
    from Axiom import Algebra, Logic

    n, m, d = Symbol(integer=True)
    f = Function(integer=True)
    Eq << apply(All[n:1:m + 1](f(n) > 0), d)

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.apply(Algebra.All.of.All.limits.subs.offset, d)

    Eq << Eq[-1].this.rhs.apply(Algebra.All.given.All.limits.subs.offset, d)


if __name__ == '__main__':
    run()
# created on 2018-12-20
