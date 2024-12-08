from util import *


@apply
def apply(given):
    x, R = given.of(Element)
    assert R in Interval.open(0, oo)
    return Element(sqrt(x), R)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x = Symbol(super_complex=True)
    Eq << apply(Element(x, Interval.open(0, oo)))

    Eq << Sets.is_positive.to.is_real.apply(Eq[0])

    Eq << Sets.In.to.Eq.definition.apply(Eq[-1])

    Eq << Eq[0].subs(Eq[-1].reversed)

    Eq << Sets.is_positive.to.Gt_0.apply(Eq[-1])

    Eq << Algebra.Gt_0.to.Gt_0.Sqrt.apply(Eq[-1], simplify=None)

    Eq << Sets.Gt_0.to.is_positive.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].subs(Eq[3])




if __name__ == '__main__':
    run()
# created on 2023-05-03
