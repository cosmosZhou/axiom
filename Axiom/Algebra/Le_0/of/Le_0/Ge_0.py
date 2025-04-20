from util import *


@apply
def apply(is_nonpositive, is_nonnegative_y):
    x = is_nonpositive.of(Expr <= 0)
    y = is_nonnegative_y.of(Expr >= 0)
    return LessEqual(x * y, 0)


@prove
def prove(Eq):
    from Axiom import Algebra, Logic
    x, y = Symbol(real=True)

    Eq << apply(x <= 0, y >= 0)

    Eq.is_zero = Imply(Equal(x, 0) & (y >= 0), x * y <= 0, plausible=True)

    Eq << Eq.is_zero.this.lhs.apply(Logic.Cond.of.And, index=0)

    Eq << Eq[-1].this.lhs * y

    Eq << Logic.Imp.given.Or_Not.apply(Eq[-1])

    Eq.is_negative = Imply((x < 0) & (y >= 0), x * y <= 0, plausible=True)

    Eq << Eq.is_negative.this.lhs.apply(Algebra.Le_0.of.Lt_0.Ge_0)

    Eq << Logic.ImpOrS.of.Imp.Imp.apply(Eq.is_zero, Eq.is_negative)

    Eq <<= Eq[0] & Eq[1]

    Eq << Logic.Cond.of.Imp.Cond.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2018-02-10
