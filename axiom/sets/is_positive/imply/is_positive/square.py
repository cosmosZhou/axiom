from util import *


@apply
def apply(given):
    x, R = given.of(Element)
    assert R in Interval.open(0, oo)
    return Element(x ** 2, R)


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol(super_complex=True)
    Eq << apply(Element(x, Interval.open(0, oo)))

    Eq << sets.is_positive.is_positive.imply.is_positive.apply(Eq[0], Eq[0])
    


if __name__ == '__main__':
    run()
# created on 2023-05-03
