from util import *


@apply
def apply(self):
    expr, (i, *ab) = self.of(Any)
    from axiom.algebra.all.then.all.limits.negate import negate
    return Any(expr._subs(i, -i), negate(i, *ab))


@prove
def prove(Eq):
    from axiom import algebra

    i, a, b = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Any[i:a:b](f(i) >= 0))

    Eq << algebra.iff.of.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.any.then.any.limits.negate)

    Eq << Eq[-1].this.lhs.apply(algebra.any.of.any.limits.negate)


if __name__ == '__main__':
    run()

# created on 2019-02-19
del oo
from . import oo
