from util import *


@apply
def apply(is_negative, lt, fx, x=None, left_open=True, right_open=True):
    from Axiom.Algebra.Le.Ge.to.Le.quadratic import quadratic_coefficient
    m, M = lt.of(Less)
    a = is_negative.of(Expr < 0)

    x, S[a], b, c = quadratic_coefficient(fx, x=x)

    y0 = a * m ** 2 + b * m + c
    y1 = a * M ** 2 + b * M + c
    interval = Interval(m, M, left_open=left_open, right_open=right_open)
    return Equal(Sup[x:interval](fx),
                 Piecewise((c - b ** 2 / (4 * a), Element(-b / (2 * a), interval)),
                           (Max(y0, y1), True)))


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    m, M, x, a, b, c = Symbol(real=True, given=True)
    Eq << apply(a < 0, m < M, a * x ** 2 + b * x + c, x)

    Eq << Algebra.Lt_0.to.Lt_0.Div.apply(Eq[0])

    Eq << Eq[2].this.lhs.apply(Algebra.Sup.eq.Add)

    Eq << Eq[-1].this.find(Max).apply(Algebra.Max.eq.Add)

    Eq << Eq[-1].this.rhs.apply(Algebra.Piece.eq.Add)

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[-1], cond=Eq[-1].find(Element))

    Eq <<= Algebra.Imply.of.Imply.subs.Bool.apply(Eq[-2]), Algebra.Imply.of.Imply.subs.Bool.apply(Eq[-1], invert=True)

    Eq <<= Algebra.Cond.Imply.of.And.Imply.And.apply(Eq[0], Eq[-2]), Eq[-1].this.lhs.apply(Sets.NotIn_Interval.to.Or)

    Eq <<= Eq[-2].this.lhs.apply(Sets.Lt_0.In.to.Eq.Sup.st.quadratic, Eq[-2].find(Sup).expr, x), Algebra.Imply_Or.of.And.Imply.apply(Eq[-1])

    Eq <<= Eq[-2].this.find(Sup).apply(Algebra.Sup.limits.subs.offset, Eq[3].lhs * -b /2), Eq[-1].this.find(Sup).apply(Algebra.Sup.limits.subs.offset, Eq[3].lhs * -b /2)

    Eq <<= Eq[-2].this.find(Sup).expr.expand(), Eq[-1].this.find(Sup).expr.expand()

    Eq <<= Eq[-2].this.find(Equal).apply(Algebra.Eq.transport, lhs=0), Eq[-1].this.find(Equal).apply(Algebra.Eq.transport, lhs=0)

    Eq <<= Eq[-2].this.lhs.apply(Algebra.Le.to.Ge_0), Eq[-1].this.lhs.apply(Algebra.Ge.to.Le_0)

    Eq <<= Eq[-2].this.rhs.rhs.apply(Algebra.Add.eq.Max), Eq[-1].this.rhs.rhs.apply(Algebra.Add.eq.Max)

    Eq << Eq[1] + Eq[3].lhs * b /2

    Eq <<= Algebra.Cond.to.Imply.And.apply(Eq[-1] & Eq[0], cond=Eq[-1].lhs >= 0), Algebra.Cond.to.Imply.And.apply(Eq[-1] & Eq[0], cond=Eq[-1].rhs <= 0)

    Eq <<= Eq[-2].this.rhs.apply(Algebra.Lt_0.Ge_0.Lt.to.Sup_Square.eq.Square), \
        Eq[-2].this.rhs.apply(Algebra.Lt_0.Ge_0.Lt.to.Max.eq.Square),\
        Eq[-1].this.rhs.apply(Algebra.Lt_0.Le_0.Lt.to.Sup_Square.eq.Square),\
        Eq[-1].this.rhs.apply(Algebra.Lt_0.Le_0.Lt.to.Max.eq.Square)

    Eq <<= Eq[-4] & Eq[-3], Eq[-2] & Eq[-1]

    Eq <<= Eq[-2].this.rhs.apply(Algebra.Eq.Eq.to.Eq.trans, reverse=True), Eq[-1].this.rhs.apply(Algebra.Eq.Eq.to.Eq.trans, reverse=True)

    Eq <<= Eq[-2].this.rhs.rhs.expand(), Eq[-1].this.rhs.rhs.expand()




if __name__ == '__main__':
    run()
# created on 2019-12-26
# updated on 2021-10-02