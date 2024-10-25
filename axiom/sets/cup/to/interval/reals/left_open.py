from util import *


@apply
def apply(self):
    interval, k = self.of(Cup[Tuple])
    S[k], S[k + 1] = interval.of(Interval)
    assert interval.left_open and not interval.right_open

    return Equal(self, Interval(-oo, oo, left_open=True))


@prove
def prove(Eq):
    from axiom import sets, algebra

    k = Symbol(integer=True)
    Eq << apply(Cup[k](Interval(k, k + 1, left_open=True)))

    Eq << sets.eq.of.et.infer.apply(Eq[0])

    x = Eq[-1].lhs
    Eq <<= sets.el_cup.of.any_el.apply(Eq[-1])

    Eq << algebra.any.of.cond.subs.apply(Eq[-1], Eq[-1].variable, Ceiling(x) - 1)

    Eq << sets.el_interval.of.et.apply(Eq[-1])

    Eq << algebra.then.gt.ceiling.apply(x)

    Eq << algebra.then.le_ceiling.apply(x)


if __name__ == '__main__':
    run()
# created on 2021-02-18
