from util import *


@apply
def apply(given):
    x = given.of(NotElement[Integers])

    return Equal(floor(-frac(x)), -1)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x = Symbol(real=True)
    Eq << apply(NotElement(x, Integers))

    Eq << Sets.NotIn.to.In.Frac.apply(Eq[0])

    Eq << Sets.In.to.In.Neg.apply(Eq[-1])

    Eq << Sets.In_Interval.to.And.apply(Eq[-1])

    Eq <<= Algebra.Lt.to.Lt.Floor.apply(Eq[-1]), Algebra.Gt.to.Ge.Floor.apply(Eq[-2])

    Eq << Algebra.Lt.to.Le.strengthen.apply(Eq[-2])

    Eq <<= Eq[-2] & Eq[-1]


if __name__ == '__main__':
    run()
# created on 2018-05-20
