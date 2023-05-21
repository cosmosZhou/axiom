from util import *


@apply
def apply(given, *limits, simplify=True):
    lhs, rhs = given.of(LessEqual)

    lhs = Limit(lhs, *limits)
    rhs = Limit(rhs, *limits)
    if simplify:
        lhs = lhs.simplify()
        rhs = rhs.simplify()
    return LessEqual(lhs, rhs)


@prove
def prove(Eq):
    from axiom import algebra, calculus

    x = Symbol(real=True)
    f, g = Function(shape=(), real=True)
    Eq << apply(LessEqual(f(x) / x, g(x) / x), (x, 0))

    Eq << algebra.le.imply.ge.reverse.apply(Eq[0])

    Eq << calculus.ge.imply.ge.limit.apply(Eq[-1], (x, 0))

    Eq << Eq[-1].reversed



if __name__ == '__main__':
    run()

# created on 2020-06-24
# updated on 2023-04-17
