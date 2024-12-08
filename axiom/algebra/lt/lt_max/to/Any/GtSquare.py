from util import *


@apply
def apply(lt, lt_max, x=None):
    U, maxi = lt_max.of(Less)
    _M, _m = maxi.of(Max[Expr ** 2, Expr ** 2])
    if x is None:
        x = lt.generate_var(real=True)
    m, M = lt.of(Less)
    assert {M, m} == {_M, _m}
    return Any[x:Interval(m, M, left_open=True, right_open=True)](x ** 2 > U)


@prove
def prove(Eq):
    from Axiom import Algebra

    m, M, U = Symbol(real=True, given=True)
    Eq << apply(m < M, U < Max(M ** 2, m ** 2))

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[-1], cond=M > 0)

    Eq <<= Algebra.Cond.of.And.Imply.split.apply(Eq[-2], cond=m > 0), Algebra.Cond.of.And.Imply.split.apply(Eq[-1], cond=m > 0)

    Eq <<= Eq[-4].this.apply(Algebra.Imply.flatten), Eq[-3].this.apply(Algebra.Imply.flatten), Eq[-2].this.apply(Algebra.Imply.flatten), Eq[-1].this.apply(Algebra.Imply.flatten)

    Eq <<= Algebra.Cond.to.Imply.And.apply(Eq[0] & Eq[1], cond=Eq[-4].lhs),\
        Algebra.Cond.to.Imply.And.apply(Eq[0] & Eq[1], cond=Eq[-3].lhs),\
        Eq[-2].this.lhs.apply(Algebra.Le.Gt.to.Lt.trans),\
        Algebra.Cond.to.Imply.And.apply(Eq[0] & Eq[1], cond=Eq[-1].lhs)

    Eq <<= Eq[-3].this.rhs.apply(Algebra.Cond.to.And.Imply.And.split, cond=M + m > 0), \
        Eq[-1].this.rhs.args[::2].apply(Algebra.Le_0.Lt.to.Eq.Max, simplify=None, ret=slice(None)), \
        Eq[-4].this.rhs.args[-1].apply(Algebra.Gt.to.Ge.relax), \
        Eq[-2].this.lhs.apply(Algebra.Lt.to.Le.relax)

    Eq <<= Algebra.Imply.to.And.Imply.apply(Eq[-4], simplify=None), \
        Eq[-3].this.rhs.args[:4:2].apply(Algebra.Eq.Cond.to.Cond.subs, simplify=None), \
        Eq[-2].this.rhs.args[::2].apply(Algebra.Ge_0.Lt.to.Eq.Max, ret=slice(None)), \
        Eq[-1].this.apply(Algebra.Imply.contraposition)

    Eq <<= Eq[-5].this.rhs.rhs.apply(Algebra.And.to.Cond, index=slice(2, None, -2), simplify=None), \
        Eq[-4].this.rhs.rhs.apply(Algebra.And.to.Cond, index=slice(3, None, -3), simplify=None), \
        Eq[-3].this.rhs.args[:3].apply(Algebra.Le_0.Lt.Lt.to.Any.GtSquare), \
        Eq[-2].this.rhs.args[::2].apply(Algebra.Eq.Cond.to.Cond.subs), \
        Algebra.Imply.of.Cond.apply(Eq[-1]).reversed

    Eq <<= Eq[-3].this.rhs.rhs.args[1].apply(Algebra.Gt.transport, lhs=0), \
        Eq[-2].this.rhs.rhs.args[2].apply(Algebra.Le.transport), \
        Eq[-1].this.rhs.apply(Algebra.Ge_0.Lt.Lt.to.Any.GtSquare)

    Eq <<= Eq[-2].this.rhs.rhs.args[1:].apply(Algebra.Le_0.Gt.to.Eq.Max, ret=1), \
        Eq[-1].this.rhs.rhs.args[1:].apply(Algebra.Gt_0.Le.to.Eq.Max, ret=0)

    Eq <<= Eq[-2].this.rhs.rhs.args[:2].apply(Algebra.Eq.Cond.to.Cond.subs), \
        Eq[-1].this.rhs.rhs.args[:2].apply(Algebra.Eq.Cond.to.Cond.subs)

    Eq <<= Eq[-2].this.rhs.apply(Algebra.Imply_And.to.Imply.And), \
        Eq[-1].this.rhs.rhs.args[1].apply(Algebra.Gt.to.Ge.relax)

    Eq.is_positive, Eq.is_nonpositive = Eq[-2].this.rhs.rhs.apply(Algebra.Le_0.Gt_0.Lt.to.Any.GtSquare),\
        Eq[-1].this.rhs.apply(Algebra.Imply_And.to.Imply.And)

    Eq <<= Eq.is_nonpositive.this.rhs.rhs.apply(Algebra.Cond.to.And.Imply.split, cond=m + M < 0)

    Eq << Eq[-1].this.rhs.apply(Algebra.Imply.to.And.Imply)

    Eq << Algebra.Imply.to.And.Imply.apply(Eq[-1], simplify=None)

    Eq <<= Eq[-1].this.rhs.rhs.apply(Algebra.And.to.Cond, index=slice(None, None, 2)), Eq[-2].this.rhs.rhs.apply(Algebra.And.to.Cond, index=0)

    Eq <<= Eq[-2].this.rhs.apply(Algebra.Imply_And.to.Imply.And), Eq[-1].this.rhs.apply(Algebra.Imply_And.to.Imply.And)

    Eq.is_negative = Eq[-2].this.rhs.rhs.apply(Algebra.Ge_0.Lt_0.Lt.to.Any.GtSquare)

    Eq << Eq[-1].this.rhs.rhs.args[0].apply(Algebra.Eq.transport, lhs=0)

    Eq << Eq[-1].this.rhs.rhs.apply(Algebra.Eq.Cond.to.Cond.subs, ret=0)

    Eq << Algebra.Imply_And.to.Imply.And.apply(Eq[-1], index=0)

    Eq << Eq[-1].this.rhs.apply(Algebra.Cond.Imply.to.Imply.And.rhs)

    Eq << Eq[-1].this.rhs.rhs.args[1:].apply(Algebra.Gt_0.Lt.to.Any.GtSquare)

    Eq << Eq[-1].this.rhs.rhs.apply(Algebra.Eq.Cond.to.Cond.subs, reverse=True)

    Eq <<= Eq[-1] & Eq.is_negative & Eq.is_positive





if __name__ == '__main__':
    run()
# created on 2019-09-08
# updated on 2023-05-18
