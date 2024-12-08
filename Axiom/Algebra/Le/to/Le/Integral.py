from util import *


@apply
def apply(given, *limits):
    lhs, rhs = given.of(LessEqual)

    return LessEqual(Integral(lhs, *limits).simplify(), Integral(rhs, *limits).simplify())


@prove
def prove(Eq):
    from Axiom import Algebra, Calculus
    x, a, b = Symbol(real=True)

    f, g = Function(shape=(), real=True)

    Eq << apply(LessEqual(f(x), g(x)), (x, a, b))

    Eq << Eq[0].apply(Algebra.Cond.to.All.restrict, (x, a, b))

    Eq << Calculus.All_Le.to.Le.Integral.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2019-10-31
