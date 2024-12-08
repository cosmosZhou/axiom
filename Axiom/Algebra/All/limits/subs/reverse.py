from util import *


@apply
def apply(self, old, new):
    from Axiom.Algebra.Sum.limits.subs.Neg import limits_subs
    return limits_subs(All, self, old, new)


@prove
def prove(Eq):
    from Axiom import Algebra

    i, a, b, c = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(All[i:a:b](f(i)), i, c - i)

    Eq << Algebra.Iff.of.And.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.All.to.All.limits.subs.reverse, i, c - i)
    Eq << Eq[-1].this.rhs.apply(Algebra.All.to.All.limits.subs.reverse, i, c - i)


if __name__ == '__main__':
    run()
# created on 2018-06-20
