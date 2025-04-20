from util import *


@apply
def apply(given):
    x = given.of(NotElement[Integers])

    return Equal(floor(-frac(x)), -1)


@prove
def prove(Eq):
    from Axiom import Set, Algebra

    x = Symbol(real=True)
    Eq << apply(NotElement(x, Integers))

    Eq << Set.Fract.In.Ioo.of.NotMem_Range.apply(Eq[0])

    Eq << Set.Neg.In.IccNegS.of.Mem_Icc.apply(Eq[-1])

    Eq << Set.And.of.Mem_Icc.apply(Eq[-1])

    Eq <<= Algebra.LtFloor.of.Lt.apply(Eq[-1]), Algebra.GeFloor.of.Gt.apply(Eq[-2])

    Eq << Algebra.Le.of.Lt.strengthen.apply(Eq[-2])

    Eq <<= Eq[-2] & Eq[-1]


if __name__ == '__main__':
    run()
# created on 2018-05-20
