from util import *


@apply
def apply(is_negative, lt, k=None):
    a = is_negative.of(Expr < 0)
    S[a], b = lt.of(Less)

    assert a.is_integer and b.is_integer
    if k is None:
        k = lt.generate_var(integer=True)
    return Equal(Cup[k:a:b](Interval(k, k + 1, left_open=True)), Interval(a, b, left_open=True))


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    a, b, k = Symbol(integer=True)
    Eq << apply(a < 0, a < b, k)

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[-1], cond=b >= 0)

    Eq <<= Algebra.Cond.to.Imply.And.apply(Eq[0], cond=Eq[-2].lhs), Algebra.Cond.to.Imply.And.apply(Eq[0] & Eq[1], cond=Eq[-1].lhs)

    Eq << Eq[-2].this.rhs.apply(Sets.Lt_0.Ge_0.to.Cup.eq.Interval.left_open)

    Eq << Eq[-1].this.rhs.apply(Sets.Lt_0.Lt_0.Lt.to.Cup.eq.Interval.left_open)





if __name__ == '__main__':
    run()
# created on 2018-10-15
# updated on 2021-11-23