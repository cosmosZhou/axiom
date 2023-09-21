from util import *


@apply
def apply(self):
    interval, (k, a, b) = self.of(Cup)
    S[k], S[k + 1] = interval.of(Interval)
    assert not interval.left_open and interval.right_open

    return Equal(self, Interval(a, b, right_open=True))


@prove
def prove(Eq):
    from axiom import algebra, sets

    k, a, b = Symbol(integer=True)
    Eq << apply(Cup[k:a:b](Interval(k, k + 1, right_open=True)))

    Eq << algebra.cond.given.et.infer.split.apply(Eq[0], cond=a < b)

    Eq << Eq[-2].this.lhs.apply(sets.lt.imply.eq.cup.to.interval.right_open, k)

    Eq << (a >= b).this.apply(sets.ge.imply.is_empty.interval, right_open=True)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(algebra.eq.cond.given.et.subs)

    Eq << algebra.infer.given.et.infer.apply(Eq[-1])

    Eq << Eq[-1].this.find(Cup).apply(sets.cup.piece)

    Eq << (a >= b).this.apply(sets.ge.imply.is_empty.range)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(algebra.eq.cond.given.et.subs)

    
    


if __name__ == '__main__':
    run()
from . import negative
# created on 2021-02-23
# updated on 2023-08-26
