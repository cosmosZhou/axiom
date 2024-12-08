from util import *


@apply
def apply(is_nonnegative, lt, left_open=True, right_open=True, x=None):
    m = is_nonnegative.of(Expr >= 0)
    S[m], M = lt.of(Less)
    if x is None:
        x = lt.generate_var(real=True)

    self = Inf[x:Interval(m, M, left_open=left_open, right_open=right_open)](x ** 2)
    return Equal(self, m ** 2)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    m, M = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(m >= 0, m < M, x=x)

    Eq << Sets.Lt.to.In.Interval.average.apply(Eq[1])

    Eq << Sets.In_Interval.to.And.apply(Eq[-1])

    Eq << Algebra.Gt.Ge.to.Gt.trans.apply(Eq[-2], Eq[0])

    Eq.eq_max = Algebra.Ge_0.Lt.to.Eq.Max.apply(Eq[0], Eq[1])

    Eq << Algebra.Ge.Lt.to.Gt.trans.apply(Eq[0], Eq[1])

    Eq.eq_abs_M = Algebra.Gt_0.to.Eq.Abs.apply(Eq[-1])

    Eq.eq_abs_m = Algebra.Ge_0.to.Eq.Abs.apply(Eq[0])

    Eq << Algebra.Eq.of.And.squeeze.apply(Eq[2])

    y = Symbol(real=True)
    Eq <<= Algebra.LeInf.of.All_Any_Lt.apply(Eq[-2], y), Algebra.GeInf.of.All.Ge.apply(Eq[-1])

    Eq <<= Algebra.All.of.And.All.split.apply(Eq[-2], cond=y <= M ** 2), Algebra.All.of.Imply.apply(Eq[-1])

    Eq <<= Algebra.All.of.Imply.apply(Eq[-3]), Eq[-2].subs(Eq.eq_max), Eq[-1].this.lhs.apply(Sets.In_Interval.to.Gt)

    Eq <<= Eq[-3].this.rhs.apply(Algebra.Any.of.Cond.subs, x, (m + sqrt(y)) / 2), Eq[-2].this.expr.apply(Algebra.Any.of.Cond.subs, x, (M + m) / 2), Eq[-1].this.lhs.apply(Algebra.Cond.to.Imply.And, cond=Eq[0])

    Eq <<= Algebra.Imply.of.And.Imply.apply(Eq[-3]), Algebra.And.of.And.apply(Eq[-2]), Algebra.Imply_Imply.of.And.Imply.apply(Eq[-1])

    Eq << Algebra.Cond.of.Cond.subs.Bool.apply(Eq[-2], cond=Eq[0], invert=True)

    Eq <<= Eq[-5].this.lhs.apply(Sets.In_Interval.to.Gt), Eq[-4].this.rhs.apply(Sets.In.of.In.Sub, m / 2), Eq[-3].this.expr.apply(Algebra.Lt.of.Gt_0), Eq[-1].this.lhs.apply(Algebra.Ge_0.Gt.to.Gt.Square)

    Eq << Eq[-1].this.lhs.apply(Algebra.Gt.to.Ge.relax)

    Eq <<= Eq[-4].this.rhs.apply(Algebra.Lt.of.Gt_0), Eq[-3].this.rhs.apply(Sets.In.of.In.Mul.Interval, 2), Algebra.All.of.Imply.apply(Eq[-2])

    Eq <<= Eq[-3].this.rhs.lhs.apply(Algebra.Sub.Square.eq.Mul), Eq[-2].this.lhs.apply(Sets.In.to.In.Sqrt), Eq[-1].this.rhs.lhs.apply(Algebra.Sub.Square.eq.Mul)

    Eq <<= Eq[-3].this.rhs.apply(Algebra.Gt_.Mul.Zero.of.And.Gt_0), Eq[-2].subs(Eq.eq_abs_m, Eq.eq_abs_M), Eq[-1].this.rhs.apply(Algebra.Gt_.Mul.Zero.of.And.Gt_0)

    Eq <<= Algebra.Imply.of.And.Imply.apply(Eq[-3]), Eq[-2].this.rhs.apply(Sets.In.of.And.strengthen, M, strict=True), Algebra.Imply.of.And.Imply.apply(Eq[-1])

    Eq <<= Eq[-4].this.rhs * 2, Eq[-5].this.rhs * 2, Algebra.Imply.of.Cond.apply(Eq[-3]), Eq[-1].this.lhs.apply(Algebra.Gt.to.Gt.Sqrt), Eq[-2].this.rhs.apply(Algebra.Gt_.Add.Zero.of.And.Gt_0, 1)

    Eq << Eq[-3] + (m - M)

    Eq <<= Eq[-5].this.lhs.apply(Algebra.Gt.to.Gt.Sqrt), Eq[-4].this.rhs.apply(Algebra.Gt_.Add.Zero.of.And), Eq[-2].subs(Eq.eq_abs_M), Algebra.Imply.of.And.Imply.apply(Eq[-1])

    Eq <<= Eq[-5].subs(Eq.eq_abs_m), Eq[-4].this.lhs.apply(Algebra.Gt.to.Gt.relax, lower=0), Eq[-3].this.rhs.apply(Algebra.Gt.transport, lhs=slice(1, None)), Algebra.Imply.of.Cond.apply(Eq[-2]), Eq[-1].this.lhs.apply(Algebra.Gt.to.Gt.relax, lower=0)

    Eq << Eq[-4].this.lhs.apply(Algebra.Gt.to.Gt_0)

    Eq << Eq[-1].this.lhs.apply(Algebra.Gt_0.to.Gt_0.Sqrt)

    Eq <<= Algebra.Imply.of.And.Imply.apply(Eq[-3]), Eq[-2].this.rhs.apply(Algebra.Gt.of.And.strengthen, M, strict=True)

    Eq <<= Algebra.Imply.of.Cond.apply(Eq[-2]), Eq[-3].this.rhs / 3, Eq[-1].this.lhs.apply(Algebra.Gt.to.Ge.relax)

    Eq << Algebra.Imply.of.Cond.apply(Eq[-1])

    Eq << Eq[-1] * 2 - M

    Eq << Eq[-1].reversed





if __name__ == '__main__':
    run()
# created on 2019-07-02
# updated on 2023-05-20
