from util import *


@apply
def apply(given):
    lhs, *limits = given.of(All[Expr < 0])

    return Less(Sum(lhs, *limits), 0)


@prove
def prove(Eq):
    from Axiom import Algebra
    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    f = Function(shape=(), complex=True)
    Eq << apply(All[i:n](f(i) < 0))

    Eq << Algebra.LtSum.of.All_Lt.apply(Eq[0])


if __name__ == '__main__':
    run()
# created on 2019-01-30
