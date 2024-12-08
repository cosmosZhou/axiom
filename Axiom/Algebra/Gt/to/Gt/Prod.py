from util import *


@apply
def apply(given, *limits):
    lhs, rhs = given.of(Greater)
    assert rhs.is_positive

    return Greater(Product(lhs, *limits).simplify(), Product(rhs, *limits).simplify())


@prove
def prove(Eq):
    from Axiom import Algebra
    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)

    f, g = Function(shape=(), real=True, positive=True)

    Eq << apply(Greater(f(i), g(i)), (i, 0, n))

    Eq << Eq[0].apply(Algebra.Cond.to.All.restrict, (i, 0, n))

    Eq << Algebra.All_Gt.to.Gt.Prod.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2019-07-24
