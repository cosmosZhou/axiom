from util import *


@apply
def apply(self):
    interval, (k, a, b) = self.of(Cup)
    S[k], S[k + 1] = interval.of(Interval)
    assert not interval.left_open and interval.right_open

    return Equal(self, Interval(a, b, right_open=True))


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    k, a, b = Symbol(integer=True)
    Eq << apply(Cup[k:a:b](Interval(k, k + 1, right_open=True)))

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[0], cond=a < b)

    Eq << Eq[-2].this.lhs.apply(Sets.Lt.to.Cup.eq.Interval.right_open, k)

    Eq << (a >= b).this.apply(Sets.Ge.to.Eq_EmptySet.Interval, right_open=True)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.Cond.of.And.subs)

    Eq << Algebra.Imply.of.And.Imply.apply(Eq[-1])

    Eq << Eq[-1].this.find(Cup).apply(Sets.Cup.Piece)

    Eq << (a >= b).this.apply(Sets.Ge.to.Eq_EmptySet.Range)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.Cond.of.And.subs)





if __name__ == '__main__':
    run()
# created on 2021-02-23
# updated on 2023-08-26

from . import negative
