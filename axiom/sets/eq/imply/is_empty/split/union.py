from util import *


@apply
def apply(given):
    x_union_abs, x_abs_sum = given.of(Equal)
    if not x_union_abs.is_Card:
        x_union_abs, x_abs_sum = x_abs_sum, x_union_abs

    A, B = x_union_abs.of(Card[Union])

    S[Card(A)] = x_abs_sum.of(Add[Card(B)])

    return Equal(A & B, A.etype.emptySet)


@prove
def prove(Eq):
    from axiom import sets, algebra

    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Equal(Card(A | B), Card(A) + Card(B)))

    Eq << sets.imply.eq.principle.inclusion_exclusion.basic.apply(A, B)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1].this.apply(algebra.eq.simplify.terms.common)

    Eq << -Eq[-1]

    Eq << Eq[-1].apply(sets.is_zero.imply.is_empty)


if __name__ == '__main__':
    run()

# created on 2021-04-04
