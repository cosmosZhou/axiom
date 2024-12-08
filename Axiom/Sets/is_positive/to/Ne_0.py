from util import *


@apply
def apply(given):
    x, R = given.of(Element)
    assert R in Interval.open(0, oo)
    return Unequal(x, 0)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x = Symbol(complex=True)
    Eq << apply(Element(x, Interval.open(0, oo)))

    Eq << Sets.is_positive.to.Gt_0.apply(Eq[0])

    Eq << Algebra.Gt_0.to.Ne_0.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-05-03
