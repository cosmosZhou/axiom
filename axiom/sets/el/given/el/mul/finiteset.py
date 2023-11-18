from util import *


@apply
def apply(given, d):
    d = sympify(d)
    assert d.is_nonzero
    e, s = given.of(Element[FiniteSet])
    return Element(e * d, FiniteSet(*(arg * d for arg in s)))


@prove
def prove(Eq):
    from axiom import sets

    x, a, b = Symbol(integer=True)
    d = Symbol(real=True, zero=False)
    Eq << apply(Element(x, {a, b}), d)

    Eq << sets.el.imply.el.mul.finiteset.apply(Eq[1], 1 / d)


if __name__ == '__main__':
    run()
# created on 2023-05-30
