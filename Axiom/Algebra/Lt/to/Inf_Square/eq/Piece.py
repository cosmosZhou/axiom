from util import *


@apply
def apply(lt, left_open=True, right_open=True, x=None):
    m, M = lt.of(Less)
    if x is None:
        x = lt.generate_var(real=True)

    self = Inf[x:Interval(m, M, left_open=left_open, right_open=right_open)](x ** 2)
    return Equal(self, Piecewise((0, (m <= 0) & (M >= 0)), (Min(m ** 2, M ** 2), True)))


@prove
def prove(Eq):
    from Axiom import Algebra

    m, M = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(m < M, x=x)

    Eq <<= Algebra.Cond.to.Imply.And.apply(Eq[0], cond=m >= 0), Algebra.Cond.to.Imply.And.apply(Eq[0], cond=M <= 0)

    Eq <<= Eq[-2].this.rhs.apply(Algebra.Ge_0.Lt.to.Inf_Square.eq.Square), Eq[-2].this.rhs.apply(Algebra.Ge_0.Lt.to.Eq.Min), \
        Eq[-1].this.rhs.apply(Algebra.Le_0.Lt.to.Inf_Square.eq.Square), Eq[-1].this.rhs.apply(Algebra.Le_0.Lt.to.Eq.Min)

    Eq <<= Eq[-3] & Eq[-4], Eq[-1] & Eq[-2]

    Eq <<= Eq[-2].this.rhs.apply(Algebra.Eq.Eq.to.Eq.subs, reverse=True), Eq[-1].this.rhs.apply(Algebra.Eq.Eq.to.Eq.subs, reverse=True)

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[1], cond=M >= 0)

    Eq <<= Algebra.Imply.of.Imply.subs.Bool.apply(Eq[-2]), Algebra.Imply.of.Imply.subs.Bool.apply(Eq[-1], invert=True)

    Eq <<= Eq[-1].this.lhs.apply(Algebra.Lt_0.to.Le_0), Algebra.Cond.of.And.Imply.split.apply(Eq[-2], cond=m <= 0)

    Eq <<= Algebra.Imply.of.Imply.subs.Bool.apply(Eq[-2]), Algebra.Imply.of.Imply.subs.Bool.apply(Eq[-1], invert=True)

    Eq <<= Eq[-2].this.apply(Algebra.Imply.flatten), Eq[-1].this.apply(Algebra.Imply.flatten)

    Eq <<= Algebra.Cond.of.And.Imply.split.apply(Eq[-2], cond=M > 0), Algebra.Imply_And.of.Imply.delete.apply(Eq[-1], 1)

    Eq <<= Eq[-3].this.apply(Algebra.Imply.flatten), Eq[-2].this.apply(Algebra.Imply.flatten), Eq[-1].this.lhs.apply(Algebra.Gt.to.Ge.relax)

    Eq <<= Eq[-2].this.lhs.apply(Algebra.Gt_0.Le_0.to.Inf_Square.eq.Zero), Algebra.Imply_And.of.Imply.And.subs.apply(Eq[-1])

    Eq << Algebra.Imply_And.of.Imply.delete.apply(Eq[-1])

    Eq <<= Algebra.Cond.Imply.of.And.Imply.And.apply(Eq[0], Eq[-1])

    Eq <<= Eq[-1].this.lhs.apply(Algebra.Eq.Cond.to.Cond.subs)

    Eq << Eq[-1].this.lhs.apply(Algebra.Lt_0.to.Inf_Square.eq.Zero, x)





if __name__ == '__main__':
    run()
# created on 2019-12-21
# updated on 2023-05-18
