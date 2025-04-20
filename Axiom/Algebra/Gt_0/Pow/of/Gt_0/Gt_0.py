from util import *


@apply
def apply(gt_zero, given):
    n = gt_zero.of(Expr > 0)
    x = given.of(Expr > 0)
    return Greater(x ** n, 0)


@prove
def prove(Eq):
    from Axiom import Algebra, Logic

    x = Symbol(real=True)
    n = Symbol(integer=True)
    Eq << apply(n > 0, x > 0)

    m = Symbol(integer=True, positive=True)
    Eq << Algebra.GtPow.of.Gt.apply(Eq[1], m)

    Eq << Algebra.All.of.Cond.apply(Eq[-1], m)

    Eq << Logic.Imp.of.All.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[-2].variable, n)

    Eq << Algebra.Ge.of.Gt.strengthen.apply(Eq[0])

    Eq << Logic.Cond.of.Imp.Cond.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2023-04-15
