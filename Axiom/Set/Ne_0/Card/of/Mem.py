from util import *


@apply
def apply(given):
    x, R = given.of(Element)
    R == Reals - {0}
    assert x.is_complex

    return Unequal(abs(x), 0)


@prove
def prove(Eq):
    from Axiom import Algebra, Logic

    x = Symbol(complex=True, given=True)
    Eq << apply(Element(x, Reals - {0}))

    Eq << ~Eq[1]

    Eq << Algebra.Eq_0.of.Norm.eq.Zero.apply(Eq[-1])

    Eq << Logic.Cond.of.Eq.Cond.subs.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()
# created on 2021-03-13
