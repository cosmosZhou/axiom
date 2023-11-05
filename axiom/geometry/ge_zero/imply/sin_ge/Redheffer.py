from util import *


@apply
def apply(ge_zero):
    x = ge_zero.of(Expr >= 0)
    return sin(x) >= x * (S.Pi ** 2 - x ** 2)/(S.Pi ** 2 + x ** 2)

@prove
def prove(Eq):
    from axiom import algebra, sets, geometry

    x = Symbol(real=True)
    Eq << apply(x >= 0)

    Eq << algebra.cond.given.et.infer.split.apply(Eq[1], cond=x > 0)

    Eq << algebra.infer.given.et.infer.split.apply(Eq[-1], cond=x >= 0)

    Eq << algebra.infer.given.infer.subs.apply(Eq[-2])

    Eq << algebra.infer.given.cond.invert.apply(Eq[-1])

    Eq.lt, Eq.ge = algebra.infer.given.et.infer.split.apply(Eq[2], cond=x < S.Pi)

    Eq << Eq.lt.this.lhs.apply(sets.lt.gt.imply.el.interval)

    Eq << Eq[-1].this.lhs.apply(geometry.el_interval.imply.sin_gt)

    Eq << Eq[-1].this.lhs.apply(algebra.gt.imply.ge.relax)

    Eq << algebra.infer.given.et.infer.split.apply(Eq.ge, cond=x > S.Pi)

    Eq << algebra.infer.given.infer.subs.apply(Eq[-1])

    t = Symbol(x - S.Pi)
    Eq << t.this.definition

    Eq << Eq[-1] + S.Pi

    Eq << Eq[-4].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.find(Greater).simplify()

    Eq << Eq[-1].this.find(Expr ** 2 - Expr ** 2).apply(algebra.sub.square.to.mul)

    Eq.le = -Eq[-1].this.rhs

    Eq.gt_1 = Infer(t > 0, Greater(Mul(*Eq.le.find(Mul).args[1:]), 1), plausible=True)

    Eq << Eq.gt_1.this.rhs * Eq[-1].find((~Expr) ** -1)

    Eq << Eq[-1].this.find(Mul).apply(algebra.mul.to.add, deep=True)

    Eq << Eq[-1].this.find(Add ** 2).apply(algebra.pow.to.add)

    Eq << algebra.infer.given.infer.et.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.gt_zero.gt.given.et.div)

    Eq << algebra.infer.imply.infer.et.apply(Eq.gt_1)

    Eq << Eq[-1].this.rhs.apply(algebra.gt_zero.gt.imply.gt.mul)

    Eq << Eq[-1].lhs.this.apply(geometry.gt_zero.imply.sin_le)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(algebra.gt.le.imply.lt.transit)

    Eq << Eq[-1].this.rhs.apply(algebra.lt.imply.le.relax)

    #reference:
    #https://www.zhihu.com/question/355479801
    #related paper:
    #https://www.zhihu.com/question/431618787
    #https://www.zhihu.com/question/534567781
    #https://www.zhihu.com/question/471643309



if __name__ == '__main__':
    run()
# created on 2023-10-03
