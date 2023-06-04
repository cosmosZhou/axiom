from util import *


@apply
def apply(given, var=None):
    S, n = given.of(Equal[Card])

    assert n.is_extended_positive
    if var is None:
        var = S.element_symbol()
    return Any[var:S](Equal(Card(S - var.set), n - 1))


@prove
def prove(Eq):
    from axiom import algebra, sets

    S = Symbol(etype=dtype.integer)
    n = Symbol(integer=True, positive=True)
    Eq << apply(Equal(Card(S), n))

    Eq << algebra.eq.imply.ge.apply(Eq[0])

    Eq << sets.ge.imply.any_el.apply(Eq[-1], simplify=False)

    Eq << sets.any_el.imply.any_el.limits_restricted.apply(Eq[-1], simplify=False)

    Eq << Eq[-1].this.expr.apply(sets.el.imply.eq.union)

    Eq << Eq[-1].this.expr.apply(sets.eq.imply.eq.card)

    Eq << Eq[-1].this.find(Card).apply(sets.card.to.add)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1].this.expr - 1

    

    
    


if __name__ == '__main__':
    run()

# created on 2020-09-07
# updated on 2023-06-01
