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

    Eq << algebra.lt.then.gt_zero.apply(Eq[0])

    Eq << algebra.gt_zero.eq.then.eq.div.apply(Eq[-1], Eq[1])

    Eq << Eq[-1].this.rhs.apply(algebra.add.to.mul)


if __name__ == '__main__':
    run()
# created on 2019-04-18
# updated on 2023-05-02
