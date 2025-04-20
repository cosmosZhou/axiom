from util import *


@apply
def apply(lt_zero, gt):
    a, b = gt.of(Greater)
    x = lt_zero.of(Expr < 0)
    return lt_zero, Less((a * x).expand(), (b * x).expand()).simplify()


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y, z = Symbol(integer=True)
    Eq << apply(x < 0, Greater(x + y, z))

    Eq << Algebra.GtDiv.of.Lt_0.Lt.apply(Eq[0], Eq[2])






if __name__ == '__main__':
    run()
# created on 2023-10-03
