from util import *


@apply
def apply(self):
    interval, (k, a, b) = self.of(Cup)
    S[k], S[k + 1] = interval.of(Interval)
    assert interval.left_open and not interval.right_open

    return Equal(self, Interval(a, b, left_open=True))


@prove
def prove(Eq):
    from axiom import algebra, sets

    k, a, b = Symbol(integer=True)
    Eq << apply(Cup[k:a:b](Interval(k, k + 1, left_open=True)))

    Eq << algebra.cond.of.et.infer.split.apply(Eq[0], cond=a < b)

    Eq << Eq[-2].this.lhs.apply(sets.lt.then.eq.cup.to.interval.left_open, k)

    Eq << (a >= b).this.apply(sets.ge.then.is_empty.interval, left_open=True)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(algebra.eq.cond.of.et.subs)

    Eq << algebra.infer.of.et.infer.apply(Eq[-1])

    Eq << Eq[-1].this.find(Cup).apply(sets.cup.piece)

    Eq << (a >= b).this.apply(sets.ge.then.is_empty.range)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(algebra.eq.cond.of.et.subs)





if __name__ == '__main__':
    run()
from . import negative
# created on 2018-10-20
# updated on 2023-08-26
