from util import *


@apply
def apply(given):
    A = given.of(Unequal[EmptySet])
    return Unequal(Card(A), 0)


@prove
def prove(Eq):
    from axiom import sets, algebra

    A = Symbol(etype=dtype.integer)
    Eq << apply(Unequal(A, A.etype.emptySet))

    Eq << sets.ne_empty.imply.any_el.apply(Eq[0], simplify=False)

    Eq << Eq[-1].this.expr.apply(sets.el.imply.eq.union)

    Eq << Eq[-1].this.expr.apply(sets.eq.imply.eq.card)

    Eq << Eq[-1].this.find(Card).apply(sets.card.to.add)

    Eq << Unequal(Eq[-1].find(Add), 0, plausible=True)

    Eq << algebra.cond.any.imply.any.et.apply(Eq[-2], Eq[-1])


    Eq << Eq[-1].this.expr.apply(algebra.eq.ne.imply.ne.transit)




if __name__ == '__main__':
    run()

# created on 2020-07-11
# updated on 2023-06-01
