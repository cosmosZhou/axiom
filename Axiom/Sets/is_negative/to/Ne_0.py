from util import *


@apply
def apply(given):
    x, R = given.of(Element)
    assert R in Interval.open(-oo, 0)
    return Unequal(x, 0)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x = Symbol(complex=True)
    Eq << apply(Element(x, Interval.open(-oo, 0)))

    Eq << Sets.is_negative.to.Lt_0.apply(Eq[0])

    Eq << Algebra.Lt_0.to.Ne_0.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-05-03