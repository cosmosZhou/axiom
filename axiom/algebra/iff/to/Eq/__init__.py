from util import *


@apply
def apply(given):
    fn, fn1 = given.of(Iff)
    return Equal(Bool(fn), Bool(fn1))


@prove
def prove(Eq):
    from Axiom import Algebra
    n = Symbol(integer=True, nonnegative=True)
    f, g = Symbol(integer=True, shape=(oo,))

    Eq << apply(Iff(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1])))

    Eq << Algebra.Iff.to.Imply.apply(Eq[0])

    Eq << Algebra.Imply.to.Eq.Bool.apply(Eq[-1])

    Eq << Algebra.Iff.to.Given.apply(Eq[0])

    Eq << Algebra.Given.to.Eq.Bool.apply(Eq[-1])

    Eq << Eq[-1] - Eq[-3]

    Eq << Algebra.Eq_0.to.Eq.apply(Eq[-1], reverse=True)


if __name__ == '__main__':
    run()

# created on 2018-01-29
from . import subs
del Sum
from . import Sum
