from util import *


@apply
def apply(given):
    x, RR = given.of(Element)
    assert Element(0, RR) == False and RR in Reals
    return Unequal(x, 0)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(complex=True)
    Eq << apply(Element(x, Reals - {0}))

    Eq << sets.is_nonzero.imply.gt_zero.abs.apply(Eq[0])

    Eq << algebra.gt_zero.imply.ne_zero.apply(Eq[-1])

    Eq << algebra.abs_ne_zero.imply.ne_zero.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-05-02
