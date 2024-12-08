from util import *


@apply
def apply(lt, x=None, left_open=True, right_open=True):
    m, M = lt.of(Less)
    return Equal(Inf[x:Interval(m, M, left_open=left_open, right_open=right_open)](x), m)


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    m, M, a, b = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(m < M, x)

    Eq.eq_max = Algebra.Lt.to.Eq.Max.apply(Eq[0])

    Eq << Algebra.Eq.of.And.squeeze.apply(Eq[-1])

    y = Symbol(real=True)
    Eq <<= Algebra.LeInf.of.All_Any_Lt.apply(Eq[-2], y), Algebra.GeInf.of.All.Ge.apply(Eq[-1])

    Eq <<= Algebra.All.of.And.All.split.apply(Eq[-2], cond=y <= M), Algebra.All.of.Or.apply(Eq[-1])

    Eq <<= Eq[-2].subs(Eq.eq_max), Eq[-3].this.expr.apply(Algebra.Any.of.Cond.subs, x, (m + y) / 2), Eq[-1].this.find(NotElement).apply(Sets.NotIn_Interval.of.Or)

    Eq <<= Eq[-2].this.expr.apply(Algebra.Any.of.Cond.subs, x, (m + M) / 2), Algebra.All_And.of.And.All.apply(Eq[-1])

    Eq <<= Algebra.And.of.And.apply(Eq[-3]), Algebra.All.of.Imply.apply(Eq[-2]), Algebra.All.of.Imply.apply(Eq[-1])

    Eq << Sets.Lt.to.In.Interval.average.apply(Eq[0])

    Eq <<= Algebra.All.of.Imply.apply(Eq[-3]), Eq[-2].this.rhs * 2, Eq[-1].this.rhs.apply(Sets.In.of.In.Mul.Interval, 2)

    Eq <<= Algebra.Cond.Imply.of.And.Imply.And.apply(Eq[0], Eq[-3]), Eq[-2].this.rhs - y, Eq[-1].this.rhs.apply(Sets.In.of.In.Sub, m)

    Eq << Eq[-2].this.lhs.apply(Sets.In_Interval.to.Gt)

    Eq <<= Eq[-3].this.lhs.apply(Algebra.Lt.Gt.to.Gt.trans, ret=1), Eq[-1].this.rhs.apply(Sets.In.of.And.strengthen, lower=M, strict=True)

    Eq <<= Eq[-2].this.lhs.apply(Algebra.Gt.Gt.to.Gt.Add), Algebra.Imply.of.Cond.apply(Eq[-1])

    Eq << Eq[-1] + (m - M)

    Eq << Eq[-2].this.rhs * 2





if __name__ == '__main__':
    run()
# created on 2019-08-27
# updated on 2023-05-12
