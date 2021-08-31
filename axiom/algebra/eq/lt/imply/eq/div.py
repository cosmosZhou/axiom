from util import *


@apply
def apply(eq, lt):
    if lt.is_Equal:
        eq, lt = lt, eq

    x, y = lt.of(Less)
    x = y - x
    lhs, rhs = eq.of(Equal)

    return Equal(lhs / x, rhs / x)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True, given=True)
    f, g, h = Function(real=True)
    Eq << apply(f(x) < g(x), Equal(g(x) * (g(x) - f(x)), h(x) * f(x) + x))

    Eq << algebra.lt.imply.is_positive.apply(Eq[0])

    Eq << algebra.is_positive.eq.imply.eq.div.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()
