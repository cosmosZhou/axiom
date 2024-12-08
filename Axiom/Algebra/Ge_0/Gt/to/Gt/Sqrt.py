from util import *


@apply
def apply(is_nonnegative, gt):
    x = is_nonnegative.of(Expr >= 0)
    y, S[x] = gt.of(Greater)
    return Greater(sqrt(y), sqrt(x))


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y = Symbol(real=True)
    Eq << apply(x >= 0, y > x)

    Eq << Algebra.Gt.Ge.to.Gt.trans.apply(Eq[1], Eq[0])

    Eq << Algebra.Gt_0.to.Gt_0.Sqrt.apply(Eq[-1])

    Eq << Algebra.Ge_0.to.Ge_0.Sqrt.apply(Eq[0])

    Eq.is_positive = Algebra.Gt.Ge.to.Gt.Add.apply(Eq[-2], Eq[-1])

    Eq << Algebra.Gt.to.Gt_0.apply(Eq[1])

    Eq << Algebra.Gt_0.Gt.to.Gt.Div.apply(Eq.is_positive, Eq[-1])

    Eq << ((sqrt(x) + sqrt(y))(-sqrt(x) + sqrt(y))).this.apply(Algebra.Mul.eq.Add, deep=True)

    Eq << Algebra.Gt_0.Eq.to.Eq.Div.apply(Eq.is_positive, Eq[-1], simplify=None)

    Eq << Eq[-3].subs(Eq[-1].reversed)

    Eq << Algebra.Gt.of.Gt_0.apply(Eq[2])




if __name__ == '__main__':
    run()
# created on 2019-06-13
# updated on 2023-05-02
