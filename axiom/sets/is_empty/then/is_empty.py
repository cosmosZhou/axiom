from util import *


@apply
def apply(given, index=0):
    args = given.of(Equal[Union, EmptySet])
    A = args[index]
    emptySet = A.etype.emptySet
    return Equal(A, emptySet)


@prove
def prove(Eq):
    from axiom import sets

    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Equal(A | B, A.etype.emptySet))

    Eq.A_nonempty = ~Eq[-1]

    Eq.A_positive = Eq.A_nonempty.apply(sets.ne_empty.then.gt_zero)

    Eq << Eq[0].apply(sets.eq.then.eq.card)

    Eq << Eq[-1].this.lhs.apply(sets.card.to.add, slice(1, None))

    Eq << sets.eq.then.eq.complement.apply(Eq[0], A)

    Eq << Eq[-1].apply(sets.eq.then.eq.card)

    Eq << Eq[-3].subs(Eq[-1])


    Eq << Eq.A_positive.subs(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2021-05-13
# updated on 2023-06-01
