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
    from Axiom import Set, Algebra

    x = Symbol(complex=True)
    Eq << apply(Element(x, Interval(-oo, oo)))

    Eq << Set.Eq.of.Mem.definition.apply(Eq[0])

    Eq << Algebra.EqConj.of.Eq.apply(Eq[-1])

    Eq << Algebra.Eq.of.Eq.Eq.apply(Eq[-1], Eq[-2])




if __name__ == '__main__':
    run()
# created on 2023-05-02
# updated on 2023-06-23
