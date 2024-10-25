from util import *


@apply
def apply(is_negative, lt, fx, x=None, left_open=True, right_open=True):
    from axiom.algebra.le.ge.then.le.quadratic import quadratic_coefficient
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
    from axiom import algebra, sets

    m, M, x, a, b, c = Symbol(real=True, given=True)
    Eq << apply(a < 0, m < M, a * x ** 2 + b * x + c, x)

    Eq << algebra.lt_zero.then.lt_zero.div.apply(Eq[0])

    Eq << Eq[2].this.lhs.apply(algebra.sup.to.add)

    Eq << Eq[-1].this.find(Max).apply(algebra.max.to.add)

    Eq << Eq[-1].this.rhs.apply(algebra.piece.to.add)

    Eq << algebra.cond.of.et.infer.split.apply(Eq[-1], cond=Eq[-1].find(Element))

    Eq <<= algebra.infer.of.infer.subs.bool.apply(Eq[-2]), algebra.infer.of.infer.subs.bool.apply(Eq[-1], invert=True)

    Eq <<= algebra.cond.infer.of.et.infer.et.apply(Eq[0], Eq[-2]), Eq[-1].this.lhs.apply(sets.notin_interval.then.ou)

    Eq <<= Eq[-2].this.lhs.apply(sets.lt_zero.el.then.eq.sup.st.quadratic, Eq[-2].find(Sup).expr, x), algebra.infer_ou.of.et.infer.apply(Eq[-1])

    Eq <<= Eq[-2].this.find(Sup).apply(algebra.sup.limits.subs.offset, Eq[3].lhs * -b /2), Eq[-1].this.find(Sup).apply(algebra.sup.limits.subs.offset, Eq[3].lhs * -b /2)

    Eq <<= Eq[-2].this.find(Sup).expr.expand(), Eq[-1].this.find(Sup).expr.expand()

    Eq <<= Eq[-2].this.find(Equal).apply(algebra.eq.transport, lhs=0), Eq[-1].this.find(Equal).apply(algebra.eq.transport, lhs=0)

    Eq <<= Eq[-2].this.lhs.apply(algebra.le.then.ge_zero), Eq[-1].this.lhs.apply(algebra.ge.then.le_zero)

    Eq <<= Eq[-2].this.rhs.rhs.apply(algebra.add.to.max), Eq[-1].this.rhs.rhs.apply(algebra.add.to.max)

    Eq << Eq[1] + Eq[3].lhs * b /2

    Eq <<= algebra.cond.then.infer.et.apply(Eq[-1] & Eq[0], cond=Eq[-1].lhs >= 0), algebra.cond.then.infer.et.apply(Eq[-1] & Eq[0], cond=Eq[-1].rhs <= 0)

    Eq <<= Eq[-2].this.rhs.apply(algebra.lt_zero.ge_zero.lt.then.eq.sup_square.to.square), \
        Eq[-2].this.rhs.apply(algebra.lt_zero.ge_zero.lt.then.eq.max.to.square),\
        Eq[-1].this.rhs.apply(algebra.lt_zero.le_zero.lt.then.eq.sup_square.to.square),\
        Eq[-1].this.rhs.apply(algebra.lt_zero.le_zero.lt.then.eq.max.to.square)

    Eq <<= Eq[-4] & Eq[-3], Eq[-2] & Eq[-1]

    Eq <<= Eq[-2].this.rhs.apply(algebra.eq.eq.then.eq.trans, reverse=True), Eq[-1].this.rhs.apply(algebra.eq.eq.then.eq.trans, reverse=True)

    Eq <<= Eq[-2].this.rhs.rhs.expand(), Eq[-1].this.rhs.rhs.expand()




if __name__ == '__main__':
    run()
# created on 2019-12-26
# updated on 2021-10-02