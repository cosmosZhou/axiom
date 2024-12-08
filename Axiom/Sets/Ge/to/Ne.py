from util import *



@apply
def apply(given):
    A_abs, positive = given.of(GreaterEqual)
    assert positive.is_positive
    A = A_abs.of(Card)

    return Unequal(A, A.etype.emptySet)


@prove
def prove(Eq):
    from Axiom import Sets
    A = Symbol(etype=dtype.integer, given=True)

    Eq << apply(Card(A) >= 1)

    Eq << ~Eq[1]

    Eq << Eq[-1].apply(Sets.Eq.to.Eq.Card)

    Eq << Eq[0].subs(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2021-04-09
