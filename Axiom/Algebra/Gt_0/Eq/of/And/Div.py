from util import *


@apply
def apply(gt, eq):
    a, b = eq.of(Equal)
    x = gt.of(Expr > 0)
    return x > 0, Equal((a / x).expand(), (b / x).expand()).simplify()


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y, z = Symbol(integer=True)
    Eq << apply(x > 0, Equal(x + y, z))

    Eq << Algebra.Gt_0.to.Ne_0.apply(Eq[0])

    Eq << Algebra.Ne_0.Eq.to.Eq.Mul.apply(Eq[-1], Eq[2])





if __name__ == '__main__':
    run()
# created on 2023-03-26
# updated on 2023-06-22