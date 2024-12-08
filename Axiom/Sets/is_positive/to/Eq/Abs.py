from util import *


@apply
def apply(given):
    x, RR = given.of(Element)
    a, b = RR.of(Interval)
    if RR.left_open:
        assert a >= 0
    else:
        assert a > 0
    return Equal(Abs(x), x)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x = Symbol(complex=True)
    Eq << apply(Element(x, Interval.open(0, oo)))

    Eq << Sets.is_positive.to.Gt_0.apply(Eq[0])

    Eq << Algebra.Gt_0.to.Eq.Abs.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-04-18
