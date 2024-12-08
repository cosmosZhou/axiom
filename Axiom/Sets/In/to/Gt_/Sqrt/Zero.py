from util import *


@apply
def apply(given):
    x, R = given.of(Element)
    assert R in Interval(-1, 1, left_open=True, right_open=True)
    return sqrt(1 - x ** 2) > 0


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x = Symbol(real=True, given=True)
    Eq << apply(Element(x, Interval(-1, 1, left_open=True, right_open=True)))

    Eq << Sets.In_Interval.to.And.apply(Eq[0])

    Eq <<= Eq[-2] + 1, Eq[-1] - 1

    Eq << -Eq[-2]

    Eq << Algebra.Lt_0.Lt_0.to.Gt_0.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul.eq.Add, deep=True)

    Eq << Algebra.Gt_0.to.Gt_0.Sqrt.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-11-26
