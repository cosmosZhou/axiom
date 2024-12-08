from util import *


@apply
def apply(given):
    fx, fy = given.of(Imply)
    return Given(fy, fx)


@prove
def prove(Eq):
    from Axiom import Algebra

    n = Symbol(integer=True)
    f, g = Function(integer=True)
    Eq << apply(Imply(f(n) < g(n), f(n + 1) < g(n + 1)))

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Imply.to.Given.reverse)

    Eq << Eq[-1].this.rhs.apply(Algebra.Imply.of.Given.reverse)


if __name__ == '__main__':
    run()
# created on 2019-10-07
