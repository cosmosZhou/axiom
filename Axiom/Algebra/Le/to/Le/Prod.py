from util import *


@apply
def apply(given, *limits):
    lhs, rhs = given.of(LessEqual)
    assert lhs.is_nonnegative
    return LessEqual(Product(lhs, *limits).simplify(), Product(rhs, *limits).simplify())


@prove
def prove(Eq):
    from Axiom import Algebra
    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)

    f, g = Function(shape=(), real=True, nonnegative=True)

    Eq << apply(LessEqual(f(i), g(i)), (i, 0, n))

    Eq << Eq[0].apply(Algebra.Cond.to.All.restrict, (i, 0, n))

    Eq << Algebra.All_Le.to.Le.Prod.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2019-11-01
