from util import *


@apply
def apply(self):
    interval, k = self.of(Cup[Tuple])
    S[k], S[k + 1] = interval.of(Interval)
    assert interval.left_open and not interval.right_open

    return Equal(self, Interval(-oo, oo, left_open=True))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    k = Symbol(integer=True)
    Eq << apply(Cup[k](Interval(k, k + 1, left_open=True)))

    Eq << Sets.Eq.of.And.Imply.apply(Eq[0])

    x = Eq[-1].lhs
    Eq <<= Sets.In_Cup.of.Any_In.apply(Eq[-1])

    Eq << Algebra.Any.of.Cond.subs.apply(Eq[-1], Eq[-1].variable, Ceiling(x) - 1)

    Eq << Sets.In_Interval.of.And.apply(Eq[-1])

    Eq << Algebra.Gt_Sub_.Ceiling.One.apply(x)

    Eq << Algebra.Le_Ceiling.apply(x)


if __name__ == '__main__':
    run()
# created on 2021-02-18
