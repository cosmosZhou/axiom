from util import *


@apply
def apply(eq_cup):
    ((b, k), (S[k], S[0], n)), X_complement = eq_cup.of(Equal[Cup[FiniteSet[Indexed]]])
    n += 1
    X = n.of(Card)

    S[X], y = X_complement.of(Complement[Basic, FiniteSet])
    assert X.is_finiteset
    return Element(y, X)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    X = Symbol(etype=dtype.real, given=True, finiteset=True)
    y = Symbol(real=True, given=True)
    b = Symbol(real=True, shape=(oo,))
    n = Card(X)
    Eq << apply(Equal(X - {y}, b[:n - 1].cup_finiteset()))

    Eq << ~Eq[1]

    Eq << Sets.NotIn.to.Eq.Complement.apply(Eq[-1])

    Eq << Eq[0].subs(Eq[-1])

    Eq << Sets.CardCup.le.Sum_Card.apply(*Eq[-1].rhs.args)

    Eq << Sets.Eq.to.Eq.Card.apply(Eq[-2])

    Eq << Algebra.Eq.Le.to.Le.subs.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2021-03-22