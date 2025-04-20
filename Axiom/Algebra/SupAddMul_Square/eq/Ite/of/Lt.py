from util import *


@apply
def apply(lt, fx, x=None, left_open=True, right_open=True):
    m, M = lt.of(Less)
    from Axiom.Algebra.Le.of.Le.Ge.quadratic import quadratic_coefficient
    x, a, b, c = quadratic_coefficient(fx, x=x)

    delta = b * b - 4 * a * c

    y0 = a * m ** 2 + b * m + c
    y1 = a * M ** 2 + b * M + c

    interval = Interval(m, M, left_open=left_open, right_open=right_open)
    return Equal(Sup[x:interval](fx),
                 Piecewise((c - b ** 2 / (4 * a), Element(-b / (2 * a), interval) & (a < 0)),
                           (Max(y0, y1), True)))


@prove
def prove(Eq):
    from Axiom import Algebra, Logic

    x, m, M, a, b, c = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(m < M, a * x ** 2 + b * x + c, x)

    Eq << Logic.Cond.given.And.Imp.split.apply(Eq[-1], cond=a >= 0)

    Eq <<= Logic.Imp.given.Imp.subs.Bool.apply(Eq[-2], invert=True), Logic.Imp.given.Imp.subs.Bool.apply(Eq[-1])

    Eq <<= Logic.Cond.given.And.Imp.split.apply(Eq[-2], cond=a > 0), Logic.Cond.Imp.given.And.Imp.And.apply(Eq[0], Eq[-1])

    Eq <<= Eq[-3].this.apply(Logic.Imp.flatten), Eq[-2].this.apply(Logic.Imp.flatten), Eq[-1].this.lhs.apply(Algebra.Sup_Add_Mul_Square.eq.IteMeM.of.Lt_0.Lt, a * x ** 2 + b * x + c, x)

    Eq << Logic.Imp.given.Imp.subs.apply(Eq[-1])

    Eq << Logic.Imp.given.Cond.apply(Eq[-1])

    Eq << Logic.Imp.And.of.Cond.apply(Eq[0], cond=a > 0)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sup.eq.MaxAddS_Mul_Square.of.Gt_0.Lt, a * x ** 2 + b * x + c, x)

    Eq << Algebra.Sup.eq.MaxAddS_Mul.of.Lt.apply(Eq[0], b * x + c, x)


if __name__ == '__main__':
    run()
# created on 2019-12-27

