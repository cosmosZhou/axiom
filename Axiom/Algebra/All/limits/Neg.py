from util import *


@apply
def apply(self):
    expr, (i, *ab) = self.of(All)
    from Axiom.Algebra.All.to.All.limits.Neg import negate
    return All(expr._subs(i, -i), negate(i, *ab))


@prove
def prove(Eq):
    from Axiom import Algebra

    i, a, b = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(All[i:a:b](f(i) >= 0))

    Eq << Algebra.Iff.of.And.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.All.to.All.limits.Neg)

    Eq << Eq[-1].this.lhs.apply(Algebra.All.of.All.limits.Neg)


if __name__ == '__main__':
    run()
# created on 2018-12-19