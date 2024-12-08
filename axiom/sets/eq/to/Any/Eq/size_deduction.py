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
    from Axiom import Algebra, Sets

    S = Symbol(etype=dtype.integer)
    n = Symbol(integer=True, positive=True)
    Eq << apply(Equal(Card(S), n))

    Eq << Algebra.Eq.to.Ge.apply(Eq[0])

    Eq << Sets.Ge.to.Any_In.apply(Eq[-1], simplify=False)

    Eq << Sets.Any_In.to.Any_In.limits_restricted.apply(Eq[-1], simplify=False)

    Eq << Eq[-1].this.expr.apply(Sets.In.to.Eq.Union)

    Eq << Eq[-1].this.expr.apply(Sets.Eq.to.Eq.Card)

    Eq << Eq[-1].this.find(Card).apply(Sets.Card.eq.Add)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1].this.expr - 1







if __name__ == '__main__':
    run()

# created on 2020-09-07
# updated on 2023-06-01
