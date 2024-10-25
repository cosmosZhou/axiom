from util import *


@apply
def apply(self):
    int0, int1 = self.of(Union)
    assert int1.left_open == int1.right_open == int0.left_open == int0.right_open
    a, b = int0.of(Interval)
    S[b], S[a] = int1.of(Interval)
    if int1.left_open:
        func = Interval.open
    else:
        func = Interval

    return Equal(self, func(Min(a, b), Max(b, a)))


@prove
def prove(Eq):
    from axiom import algebra, sets

    a, b = Symbol(real=True)
    Eq << apply(Interval(a, b) | Interval(b, a))

    Eq << algebra.cond.of.et.infer.split.apply(Eq[0], cond=a > b)

    Eq << Infer(a > b, Equal(Min(a, b), b), plausible=True)

    Eq << Eq[-1].this.lhs.apply(algebra.gt.then.eq.min)

    Eq <<= Eq[1] & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(algebra.eq.cond.of.et.subs)

    Eq << algebra.infer.of.et.infer.apply(Eq[-1])

    Eq << Infer(a > b, Equal(Max(a, b), a), plausible=True)

    Eq << Eq[-1].this.lhs.apply(algebra.gt.then.eq.max)

    Eq <<= Eq[-2] & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(algebra.eq.cond.of.et.subs)

    Eq << algebra.infer.of.et.infer.apply(Eq[-1])

    Eq << Infer(a > b, Equal(Interval(a, b), a.emptySet), plausible=True)

    Eq << Eq[-1].this.lhs.apply(sets.gt.then.is_empty.interval)

    Eq <<= Eq[-2] & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(algebra.eq.cond.of.et.subs)

    Eq << Infer(a <= b, Equal(Max(a, b), b), plausible=True)

    Eq << Eq[-1].this.lhs.apply(algebra.le.then.eq.max)

    Eq <<= Eq[2] & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(algebra.eq.cond.of.et.subs)

    Eq << algebra.infer.of.et.infer.apply(Eq[-1])

    Eq << Infer(a <= b, Equal(Min(a, b), a), plausible=True)

    Eq << Eq[-1].this.lhs.apply(algebra.le.then.eq.min)

    Eq <<= Eq[-2] & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(algebra.eq.cond.of.et.subs)

    Eq << algebra.infer.of.et.infer.apply(Eq[-1])

    Eq << Infer(a <= b, Subset(Interval(b, a), Interval(a, b)), plausible=True)

    Eq << Eq[-1].this.lhs.apply(sets.le.then.subset.interval)

    Eq << Eq[-1].this.rhs.apply(sets.subset.then.eq.union)





if __name__ == '__main__':
    run()
# created on 2020-06-04
from . import abs
# updated on 2023-08-26
