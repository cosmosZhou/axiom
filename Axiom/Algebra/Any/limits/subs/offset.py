from util import *


@apply
def apply(self, index=0, offset=None):
    from Axiom.Algebra.Sum.limits.subs.offset import limits_subs
    return limits_subs(Any, self, index, offset)


@prove
def prove(Eq):
    from Axiom import Algebra, Logic

    n = Symbol(integer=True)
    m, d = Symbol(integer=True, given=True)
    f = Function(integer=True)
    Eq << apply(Any[n:1:m + 1](f(n) > 0), d)

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.apply(Algebra.Any.of.Any.limits.subs.offset, d)
    Eq << Eq[-1].this.lhs.apply(Algebra.Any.of.Any.limits.subs.offset, -d)


if __name__ == '__main__':
    run()
# created on 2019-02-21
