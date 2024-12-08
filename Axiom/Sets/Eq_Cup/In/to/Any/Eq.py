from util import *


@apply
def apply(eq, contains):
    (ai, (i, S[0], n)), X = eq.of(Equal[Cup[FiniteSet]])
    S[X] = n.of(Card)

    x, S[X] = contains.of(Element)

    return Any[i:n](Equal(x, ai))


@prove
def prove(Eq):
    from Axiom import Sets

    X = Symbol(etype=dtype.real, empty=False)
    x = Symbol(real=True)
    a = Symbol(real=True, shape=(oo,))
    f = Function(real=True)
    Eq << apply(Equal(X, a[:Card(X)].cup_finiteset()), Element(x, X))

    Eq << Eq[1].subs(Eq[0])
    Eq << Sets.In_Cup.to.Any_In.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-03-22
