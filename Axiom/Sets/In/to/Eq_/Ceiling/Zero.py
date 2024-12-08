from util import *


@apply
def apply(contains):
    x, domain = contains.of(Element)
    assert domain in Interval(-1, 0, left_open=True)
    return Equal(Ceiling(x), 0)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x = Symbol(real=True)
    Eq << apply(Element(x, Interval(-1, 0, left_open=True)))

    Eq << Sets.In.to.In.Neg.apply(Eq[0])

    Eq << Sets.In.to.Eq_.Floor.Zero.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Algebra.Floor.eq.Neg.Ceiling)
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2018-10-22
