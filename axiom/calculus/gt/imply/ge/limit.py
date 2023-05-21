from util import *


@apply
def apply(given, *limits):
    lhs, rhs = given.of(Greater)

    return GreaterEqual(Limit(lhs, *limits).simplify(), Limit(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import algebra, calculus

    x = Symbol(real=True)
    f, g = Function(shape=(), real=True)
    Eq << apply(Greater(f(x) / x, g(x) / x), (x, 0))

    Eq << algebra.gt.imply.ge.relax.apply(Eq[0])

    Eq << calculus.ge.imply.ge.limit.apply(Eq[-1], (x, 0))

    Eq << Eq[-1].reversed
    


if __name__ == '__main__':
    run()

# created on 2021-08-29
# updated on 2023-04-17
