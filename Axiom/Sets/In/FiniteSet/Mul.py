from util import *


@apply
def apply(given, d):
    d = sympify(d)
    e, finiteset = given.of(Element[FiniteSet])
    assert d.is_nonzero
    return Element(e * d, FiniteSet(*(arg * d for arg in finiteset)))


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    e, a, b, c = Symbol(integer=True)
    d = Symbol(real=True, zero=False)
    Eq << apply(Element(e, {a, b, c}), d)

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Sets.In.to.In.Mul.FiniteSet, d)

    Eq << Eq[-1].this.rhs.apply(Sets.In.of.In.Mul.FiniteSet, d)




if __name__ == '__main__':
    run()
# created on 2023-05-30
