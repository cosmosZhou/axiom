from util import *


@apply
def apply(given):
    x, X = given.of(Element)

    return Equal(Card(X - {x}), Card(X) - 1)


@prove
def prove(Eq):
    from axiom import sets

    e = Symbol(integer=True)
    s = Symbol(etype=dtype.integer)
    Eq << apply(Element(e, s))

    Eq << sets.el.then.subset.apply(Eq[0], simplify=False)

    Eq << sets.subset.then.eq.union.apply(Eq[-1])

    Eq << sets.eq.then.eq.card.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(sets.card.to.add)


    Eq << Eq[-1] - 1




if __name__ == '__main__':
    run()
# created on 2021-03-07
# updated on 2023-06-01
