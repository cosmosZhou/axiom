from util import *


@apply
def apply(given, *limits):
    lhs, rhs = given.of(GreaterEqual)
    assert rhs.is_nonnegative

    return GreaterEqual(Product(lhs, *limits).simplify(), Product(rhs, *limits).simplify())


@prove
def prove(Eq):
    from Axiom import Algebra
    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)

    f, g = Function(shape=(), real=True, nonnegative=True)

    Eq << apply(GreaterEqual(f(i), g(i)), (i, 0, n))

    Eq << Eq[0].apply(Algebra.All.of.Cond.restrict, (i, 0, n))

    Eq << Algebra.GeProd.of.All_Ge.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2019-05-29
