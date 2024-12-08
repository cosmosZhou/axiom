from util import *


@apply
def apply(gt_zero, given):
    n = gt_zero.of(Expr > 0)
    x = given.of(Expr > 0)
    return Greater(x ** n, 0)


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(real=True)
    n = Symbol(integer=True)
    Eq << apply(n > 0, x > 0)

    m = Symbol(integer=True, positive=True)
    Eq << Algebra.Gt.to.Gt.Pow.apply(Eq[1], m)

    Eq << Algebra.Cond.to.All.apply(Eq[-1], m)

    Eq << Algebra.All.to.Imply.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[-2].variable, n)

    Eq << Algebra.Gt.to.Ge.strengthen.apply(Eq[0])

    Eq << Algebra.Cond.Imply.to.Cond.trans.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2023-04-15
