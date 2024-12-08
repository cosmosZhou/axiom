from util import *


@apply
def apply(given, reverse=False):
    x, R = given.of(Element)
    assert R in Reals
    if reverse:
        return Equal(x, ~x)
    return Equal(~x, x)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x = Symbol(complex=True)
    Eq << apply(Element(x, Interval(-oo, oo)))

    Eq << Sets.In.to.Eq.definition.apply(Eq[0])

    Eq << Algebra.Eq.to.Eq.Conj.apply(Eq[-1])

    Eq << Algebra.Eq.Eq.to.Eq.trans.apply(Eq[-1], Eq[-2])




if __name__ == '__main__':
    run()
# created on 2023-05-02
# updated on 2023-06-23
