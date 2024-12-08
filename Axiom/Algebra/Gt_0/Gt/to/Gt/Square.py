from util import *


@apply
def apply(is_positive_x, strict_greater_than):
    x = is_positive_x.of(Expr > 0)
    y, S[x] = strict_greater_than.of(Greater)
    return Greater(y ** 2, x ** 2)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, a, y = Symbol(real=True)
    Eq << apply(x > 0, y > x)

    Eq << Eq[1] + x

    Eq << Eq[0] * 2

    Eq << Algebra.Gt.Gt.to.Gt.trans.apply(Eq[-1], Eq[-2])

    Eq << Algebra.Gt.to.Gt_0.apply(Eq[1])

    Eq << Algebra.Gt_0.Gt_0.to.Gt_0.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul.eq.Add, deep=True)

    Eq << Eq[-1].this.apply(Algebra.Gt.transport, lhs=1)




if __name__ == '__main__':
    run()
# created on 2019-08-10
# updated on 2023-05-20
