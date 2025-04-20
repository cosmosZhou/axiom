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
    from Axiom import Algebra

    x = Symbol(real=True, given=True)
    f, g, h = Function(real=True)
    Eq << apply(f(x) < g(x), Equal(g(x) * (g(x) - f(x)), h(x) * f(x) + x))

    Eq << Algebra.Gt_0.of.Lt.apply(Eq[0])

    Eq << Algebra.EqDiv.of.Gt_0.Eq.apply(Eq[-1], Eq[1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Add.eq.Mul)


if __name__ == '__main__':
    run()
# created on 2019-04-18
# updated on 2023-05-02
