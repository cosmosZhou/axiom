from util import *


@apply
def apply(given):
    x = given.of(NotElement[Integers])

    return Unequal(frac(x), 0)


@prove
def prove(Eq):
    from Axiom import Sets

    x = Symbol(real=True, given=True)
    Eq << apply(NotElement(x, Integers))

    Eq << ~Eq[1]

    Eq << Sets.Eq_.Frac.Zero.to.In.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()
# created on 2018-05-10