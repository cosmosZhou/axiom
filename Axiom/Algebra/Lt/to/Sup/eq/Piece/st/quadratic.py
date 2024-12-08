from util import *


@apply
def apply(lt, fx, x=None, left_open=True, right_open=True):
    m, M = lt.of(Less)
    from Axiom.Algebra.Le.Ge.to.Le.quadratic import quadratic_coefficient
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
    from Axiom import Algebra

    x, m, M, a, b, c = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(m < M, a * x ** 2 + b * x + c, x)

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[-1], cond=a >= 0)

    Eq <<= Algebra.Imply.of.Imply.subs.Bool.apply(Eq[-2], invert=True), Algebra.Imply.of.Imply.subs.Bool.apply(Eq[-1])

    Eq <<= Algebra.Cond.of.And.Imply.split.apply(Eq[-2], cond=a > 0), Algebra.Cond.Imply.of.And.Imply.And.apply(Eq[0], Eq[-1])

    Eq <<= Eq[-3].this.apply(Algebra.Imply.flatten), Eq[-2].this.apply(Algebra.Imply.flatten), Eq[-1].this.lhs.apply(Algebra.Lt_0.Lt.to.Eq.Sup.st.quadratic, a * x ** 2 + b * x + c, x)

    Eq << Algebra.Imply.of.Imply.subs.apply(Eq[-1])

    Eq << Algebra.Imply.of.Cond.apply(Eq[-1])

    Eq << Algebra.Cond.to.Imply.And.apply(Eq[0], cond=a > 0)

    Eq << Eq[-1].this.rhs.apply(Algebra.Gt_0.Lt.to.Eq.Sup.st.quadratic, a * x ** 2 + b * x + c, x)

    Eq << Algebra.Lt.to.Sup.eq.Max.st.simple.apply(Eq[0], b * x + c, x)


if __name__ == '__main__':
    run()
# created on 2019-12-27
