from util import *


@apply
def apply(self):
    expr, (i, *ab) = self.of(All)
    from axiom.algebra.all.then.all.limits.negate import negate
    return All(expr._subs(i, -i), negate(i, *ab))


@prove
def prove(Eq):
    from axiom import algebra

    i, a, b = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(All[i:a:b](f(i) >= 0))

    Eq << algebra.iff.of.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.all.then.all.limits.negate)

    Eq << Eq[-1].this.lhs.apply(algebra.all.of.all.limits.negate)


if __name__ == '__main__':
    run()
# created on 2018-12-19
