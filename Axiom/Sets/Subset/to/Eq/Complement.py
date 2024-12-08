from util import *


@apply
def apply(given):
    A, B = given.of(Subset)
    assert A.is_finiteset or B.is_finiteset
    return Equal(Card(B - A), Card(B) - Card(A))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    A = Symbol(etype=dtype.integer, finiteset=True)
    B = Symbol(etype=dtype.integer)
    Eq << apply(Subset(A, B, evaluate=False))

    Eq << Sets.Card.eq.Add.split.apply(Card(B), A).reversed

    Eq << Sets.Subset.to.Eq.Intersect.apply(Eq[0])

    Eq << Eq[-1].apply(Sets.Eq.to.Eq.Card)

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Algebra.Eq.to.Eq.transport.apply(Eq[-1], lhs=0)





if __name__ == '__main__':
    run()

# created on 2021-06-26
# updated on 2023-06-01
