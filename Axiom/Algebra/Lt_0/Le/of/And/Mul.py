from util import *


@apply
def apply(lt, le):
    a, b = le.of(LessEqual)
    x = lt.of(Expr < 0)
    return lt, GreaterEqual((a * x).expand(), (b * x).expand()).simplify()


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y, z = Symbol(integer=True)
    Eq << apply(x < 0, LessEqual(x + y, z))

    Eq << Algebra.Lt_0.Ge.to.Le.Div.apply(Eq[0], Eq[2])

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul.eq.Add)




if __name__ == '__main__':
    run()
# created on 2023-10-03