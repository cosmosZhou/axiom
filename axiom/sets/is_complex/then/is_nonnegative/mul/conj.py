from util import *


@apply
def apply(is_complex):
    x, C = is_complex.of(Element)
    assert C in S.Complexes
    return Element(x * ~x, Interval(0, oo))


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(super_complex=True)
    Eq << apply(Element(x, S.Complexes))

    Eq << sets.el.then.eq.definition.apply(Eq[0])

    Eq << Eq[-1].this.lhs.apply(algebra.expr.to.add.complex)

    Eq << Eq[1].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.add, deep=True)


if __name__ == '__main__':
    run()
# created on 2023-05-03
