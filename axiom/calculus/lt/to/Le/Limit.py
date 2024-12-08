from util import *


@apply
def apply(given, *limits):
    lhs, rhs = given.of(Less)

    return LessEqual(Limit(lhs, *limits).simplify(), Limit(rhs, *limits).simplify())


@prove
def prove(Eq):
    from Axiom import Algebra, Calculus

    x = Symbol(real=True)
    f, g = Function(shape=(), real=True)
    Eq << apply(Less(f(x) / x, g(x) / x), (x, 0))

    Eq << Algebra.Lt.to.Le.relax.apply(Eq[0])

    Eq << Calculus.Le.to.Le.Limit.apply(Eq[-1], (x, 0))

    Eq << Eq[-1].reversed



if __name__ == '__main__':
    run()

# created on 2021-09-27
# updated on 2023-04-17
