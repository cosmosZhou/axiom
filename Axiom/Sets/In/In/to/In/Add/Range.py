from util import *


@apply
def apply(el1, el2):
    x0, S0 = el1.of(Element)
    x1, S1 = el2.of(Element)

    assert S0.is_Range and S1.is_Range

    return Element(x0 + x1, S0 + S1)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    a, b, c, d, x0, x1 = Symbol(integer=True)
    Eq << apply(Element(x0, Range(a, b)), Element(x1, Range(c, d)))

    Eq << Sets.In_Range.to.And.apply(Eq[0])

    Eq << Algebra.Lt.to.Le.strengthen.apply(Eq[-1])

    Eq << Sets.In_Range.to.And.apply(Eq[1])

    Eq << Algebra.Lt.to.Le.strengthen.apply(Eq[-1])

    Eq <<= Eq[-1] + Eq[-4], Eq[-3] + Eq[3]

    Eq << Sets.Le.Ge.to.In.Range.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-02-25
