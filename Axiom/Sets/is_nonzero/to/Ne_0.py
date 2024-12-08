from util import *


@apply
def apply(given):
    x, RR = given.of(Element)
    assert Element(0, RR) == False and RR in Reals
    return Unequal(x, 0)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x = Symbol(complex=True)
    Eq << apply(Element(x, Reals - {0}))

    Eq << Sets.is_nonzero.to.Gt_0.Abs.apply(Eq[0])

    Eq << Algebra.Gt_0.to.Ne_0.apply(Eq[-1])

    Eq << Algebra.Ne_.Abs.Zero.to.Ne_0.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-05-02
