from util import *


@apply
def apply(given):
    x, R = given.of(Element)
    R == Reals - {0}
    assert x.is_complex

    return Unequal(abs(x), 0)


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(complex=True, given=True)
    Eq << apply(Element(x, Reals - {0}))

    Eq << ~Eq[1]

    Eq << Algebra.Eq_.Abs.Zero.to.Eq_0.apply(Eq[-1])

    Eq << Algebra.Eq.Cond.to.Cond.subs.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()
# created on 2021-03-13
