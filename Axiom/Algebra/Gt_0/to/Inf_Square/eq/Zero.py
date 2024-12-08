from util import *


@apply
def apply(is_positive, left_open=True, right_open=True, x=None):
    M = is_positive.of(Expr > 0)
    if x is None:
        x = M.generate_var(real=True)

    self = Inf[x:Interval(0, M, left_open=left_open, right_open=right_open)](x ** 2)
    return Equal(self, 0)


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    M = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(M > 0, x=x)

    Eq << Algebra.Gt_0.to.Eq.Abs.apply(Eq[0])

    Eq << Algebra.Eq.of.And.squeeze.apply(Eq[1])

    t = Symbol(real=True)
    Eq <<= Algebra.LeInf.of.All_Any_Lt.apply(Eq[-2], t), Algebra.GeInf.of.All.Ge.apply(Eq[-1])

    Eq << Algebra.All.of.And.All.split.apply(Eq[-1], cond=t <= M ** 2)

    Eq <<= Eq[-2].this.expr.apply(Algebra.Any.of.Cond.subs, x, sqrt(t) / 2)

    Eq <<= Eq[-1].this.find(Less).apply(Algebra.Lt.of.Gt_0), Eq[-2].this.expr.apply(Algebra.Any.of.Cond.subs, x, M / 2)

    Eq <<= Eq[-2].this.find(Greater) * Rational(4, 3), Eq[-1].this.args[0].apply(Sets.In_Interval.of.And)

    Eq <<= Algebra.All_And.of.And.All.apply(Eq[-2]), Eq[-1].this.args[0].apply(Algebra.Lt.of.Gt_0)

    Eq <<= Algebra.All.of.Or.apply(Eq[-3]), Eq[-2].this.expr.apply(Sets.In_Interval.of.And), Algebra.And.of.And.apply(Eq[-1])

    Eq <<= Eq[-4].this.args[1].apply(Sets.NotIn_Interval.of.Or)

    Eq <<= Algebra.All.of.Imply.apply(Eq[-3]), Eq[-2] * 2, Algebra.All.of.Imply.apply(Eq[-1])

    Eq <<= Eq[-2].this.lhs.apply(Sets.In_Interval.to.And), Eq[-1].this.rhs * 4

    Eq <<= Eq[-2].this.lhs.apply(Algebra.Gt_0.Le.to.Le.Sqrt, ret=0), Eq[-1].this.rhs.reversed

    Eq <<= Eq[-2].subs(Eq[2]), Eq[-1].this.lhs.apply(Algebra.Gt.to.Gt.relax, lower=0, ret=0)

    Eq <<= Eq[-2].this.lhs.args[0].apply(Algebra.Gt_0.to.Gt_0.Sqrt), Eq[-1].this.lhs.args[0].apply(Algebra.Gt_0.to.Gt.scale, 4)

    Eq <<= Eq[-1].this.lhs.apply(Algebra.Gt.Gt.to.Gt.trans)

    Eq <<= Algebra.Imply.of.And.Imply.apply(Eq[-2])

    Eq <<= Eq[-2].this.lhs.args[0].apply(Algebra.Gt_0.to.Lt.scale, S.One / 2), Algebra.Imply_And.of.Imply.delete.apply(Eq[-1])

    Eq <<= Eq[-2].this.lhs.apply(Algebra.Le.Lt.to.Lt.trans)

    Eq <<= Eq[-1].this.lhs / 2


if __name__ == '__main__':
    run()
# created on 2019-08-15
