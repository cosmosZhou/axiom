from util import *


@apply
def apply(self):
    interval, k = self.of(Cup[Tuple])
    S[k], S[k + 1] = interval.of(Interval)
    assert not interval.left_open and interval.right_open

    return Equal(self, Interval.open(-oo, oo))


@prove
def prove(Eq):
    from Axiom import Sets

    k = Symbol(integer=True)
    Eq << apply(Cup[k](Interval(k, k + 1, right_open=True)))

    Eq << Eq[0].this.lhs.apply(Sets.Cup.eq.Union.split, cond=k >= 0)

    Eq << Eq[-1].this.find(Cup | ~Cup).apply(Sets.Cup.limits.subs.Neg, k, -k - 1)

    Eq << Eq[-1].this.find(Cup).apply(Sets.Cup.eq.Interval.oo.right_open)

    Eq << Eq[-1].this.find(Cup).apply(Sets.Cup.eq.Interval.minus_oo.right_open)





if __name__ == '__main__':
    run()
# created on 2021-02-18
# updated on 2023-05-13
