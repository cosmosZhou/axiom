from util import *


@apply
def apply(given):
    x, R = given.of(Element)
    assert R in Interval.open(-oo, 0)
    return Element(abs(x), -R)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x = Symbol(complex=True)
    Eq << apply(Element(x, Interval.open(-oo, 0)))

    Eq << Sets.is_negative.to.Lt_0.apply(Eq[0])

    Eq << Algebra.Lt_0.to.Eq.Abs.apply(Eq[-1])

    Eq << Eq[1].subs(Eq[-1])

    Eq << Sets.In.to.In.Neg.apply(Eq[0], simplify=None)




if __name__ == '__main__':
    run()
# created on 2020-04-15
# updated on 2023-04-18
