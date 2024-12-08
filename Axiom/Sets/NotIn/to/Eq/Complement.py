from util import *


# given e not in S


# => S - {e} = S
@apply
def apply(given):
    e, S = given.of(NotElement)
    return Equal(S - {e}, S)


@prove
def prove(Eq):
    from Axiom import Sets

    S = Symbol(etype=dtype.integer)
    e = Symbol(integer=True)
    Eq << apply(NotElement(e, S))

    Eq << Sets.NotIn.to.Eq_EmptySet.Intersect.apply(Eq[0])

    Eq << Sets.Intersect_Eq_EmptySet.to.Eq.Complement.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2019-02-01
