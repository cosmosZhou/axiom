from util import *


@apply
def apply(A, B):
    return LessEqual(Card(Intersection(A, B)), Card(A))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra
    A, B = Symbol(etype=dtype.integer)
    Eq << apply(A, B)

    Eq << Sets.CardUnion.eq.Sub_.AddCards.CardIntersect.principle.inclusion_exclusion.apply(A, B).reversed

    Eq << Sets.CardUnion.ge.Card.apply(B, A)

    Eq << Eq[-1] + Eq[-2]

    Eq << Eq[-1] - Eq[-1].lhs.args[1]

    Eq << Eq[-1].reversed

    Eq << Eq[-1].this.apply(Algebra.Le.simp.terms.common)

    Eq << Eq[-1].this.apply(Algebra.Ge_0.to.Le)


if __name__ == '__main__':
    run()

# created on 2021-04-24
