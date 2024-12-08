from util import *


@apply
def apply(is_positive, ge):
    a = is_positive.of(Expr < 0)
    x, a = ge.of(LessEqual)

    return GreaterEqual(1 / x, 1 / a)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, a = Symbol(real=True, given=True)
    Eq << apply(a < 0, x <= a)

    Eq << ~Eq[-1]

    Eq << Algebra.Lt_0.to.Ne_0.apply(Eq[0])

    Eq << Algebra.Cond.Or.to.Cond.apply(Eq[-1], Eq[-2])

    Eq.x_is_negative = Algebra.Lt.Le.to.Lt.trans.apply(Eq[0], Eq[1])

    Eq << Algebra.Lt_0.to.Ne_0.apply(Eq.x_is_negative)

    Eq << Algebra.Cond.Or.to.Cond.apply(Eq[-1], Eq[-2])

    Eq << Algebra.Lt_0.Lt_0.to.Gt_0.apply(Eq[0], Eq.x_is_negative)

    Eq << ~Algebra.Gt_0.Lt.to.Lt.Mul.apply(Eq[-1], Eq[-2]).reversed


if __name__ == '__main__':
    run()
# created on 2020-01-21
