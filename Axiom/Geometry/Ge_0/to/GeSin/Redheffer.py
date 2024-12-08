from util import *


@apply
def apply(ge_zero):
    x = ge_zero.of(Expr >= 0)
    return sin(x) >= x * (S.Pi ** 2 - x ** 2)/(S.Pi ** 2 + x ** 2)

@prove
def prove(Eq):
    from Axiom import Algebra, Sets, Geometry

    x = Symbol(real=True)
    Eq << apply(x >= 0)

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[1], cond=x > 0)

    Eq << Algebra.Imply.of.And.Imply.split.apply(Eq[-1], cond=x >= 0)

    Eq << Algebra.Imply.of.Imply.subs.apply(Eq[-2])

    Eq << Algebra.Imply.of.Cond.invert.apply(Eq[-1])

    Eq.lt, Eq.ge = Algebra.Imply.of.And.Imply.split.apply(Eq[2], cond=x < S.Pi)

    Eq << Eq.lt.this.lhs.apply(Sets.Lt.Gt.to.In.Interval)

    Eq << Eq[-1].this.lhs.apply(Geometry.In_Interval.to.GtSin)

    Eq << Eq[-1].this.lhs.apply(Algebra.Gt.to.Ge.relax)

    Eq << Algebra.Imply.of.And.Imply.split.apply(Eq.ge, cond=x > S.Pi)

    Eq << Algebra.Imply.of.Imply.subs.apply(Eq[-1])

    t = Symbol(x - S.Pi)
    Eq << t.this.definition

    Eq << Eq[-1] + S.Pi

    Eq << Eq[-4].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.find(Greater).simplify()

    Eq << Eq[-1].this.find(Expr ** 2 - Expr ** 2).apply(Algebra.Sub.Square.eq.Mul)

    Eq.le = -Eq[-1].this.rhs

    Eq.gt_1 = Imply(t > 0, Greater(Mul(*Eq.le.find(Mul).args[1:]), 1), plausible=True)

    Eq << Eq.gt_1.this.rhs * Eq[-1].find((~Expr) ** -1)

    Eq << Eq[-1].this.find(Mul).apply(Algebra.Mul.eq.Add, deep=True)

    Eq << Eq[-1].this.find(Add ** 2).apply(Algebra.Pow.eq.Add)

    Eq << Algebra.Imply.of.Imply.And.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Gt_0.Gt.of.And.Div)

    Eq << Algebra.Imply.to.Imply.And.apply(Eq.gt_1)

    Eq << Eq[-1].this.rhs.apply(Algebra.Gt_0.Gt.to.Gt.Mul)

    Eq << Eq[-1].lhs.this.apply(Geometry.Gt_0.to.LeSin)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(Algebra.Gt.Le.to.Lt.trans)

    Eq << Eq[-1].this.rhs.apply(Algebra.Lt.to.Le.relax)

    # reference:
    # https://www.zhihu.com/question/355479801
    # related paper:
    # https://www.zhihu.com/question/431618787
    # https://www.zhihu.com/question/534567781
    # https://www.zhihu.com/question/471643309



if __name__ == '__main__':
    run()
# created on 2023-10-03
