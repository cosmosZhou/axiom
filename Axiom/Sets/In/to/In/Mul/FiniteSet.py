from util import *


@apply
def apply(given, d):
    d = sympify(d)
    assert d.is_nonzero
    e, s = given.of(Element[FiniteSet])
    return Element(e * d, FiniteSet(*(arg * d for arg in s)))


@prove
def prove(Eq):
    from Axiom import Sets

    x, a, b = Symbol(integer=True)
    d = Symbol(real=True, zero=False)
    Eq << apply(Element(x, {a, b}), d)

    Eq << Sets.In_FiniteSet.of.Or.Eq.apply(Eq[1])

    Eq << Sets.In_FiniteSet.to.Or.Eq.apply(Eq[0])

    Eq << Eq[-1].this.args[0] * d

    Eq << Eq[-1].this.args[0] * d


if __name__ == '__main__':
    run()
# created on 2023-05-30