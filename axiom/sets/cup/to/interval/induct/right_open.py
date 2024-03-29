from util import *


@apply
def apply(self):
    interval, (k, S[0], n) = self.of(Cup)
    S[k], S[k + 1] = interval.of(Interval)
    assert not interval.left_open and interval.right_open

    return Equal(self, Interval(0, n, right_open=True))


@prove
def prove(Eq):
    from axiom import sets, algebra

    n = Symbol(integer=True, positive=True, given=False)
    k = Symbol(integer=True)
    Eq << apply(Cup[k:n](Interval(k, k + 1, right_open=True)))

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.apply(sets.cup.to.union.split, cond={n})

    Eq << sets.eq.imply.eq.union.apply(Eq[0], Interval(n, n + 1, right_open=True))

    Eq << Infer(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.infer.imply.eq.induct.apply(Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()
# created on 2021-02-12
