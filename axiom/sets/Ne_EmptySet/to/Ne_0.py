from util import *


@apply
def apply(given):
    A = given.of(Unequal[EmptySet])
    return Unequal(Card(A), 0)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    A = Symbol(etype=dtype.integer)
    Eq << apply(Unequal(A, A.etype.emptySet))

    Eq << Sets.Ne_EmptySet.to.Any_In.apply(Eq[0], simplify=False)

    Eq << Eq[-1].this.expr.apply(Sets.In.to.Eq.Union)

    Eq << Eq[-1].this.expr.apply(Sets.Eq.to.Eq.Card)

    Eq << Eq[-1].this.find(Card).apply(Sets.Card.eq.Add)

    Eq << Unequal(Eq[-1].find(Add), 0, plausible=True)

    Eq << Algebra.Cond.Any.to.Any.And.apply(Eq[-2], Eq[-1])


    Eq << Eq[-1].this.expr.apply(Algebra.Eq.Ne.to.Ne.trans)




if __name__ == '__main__':
    run()

# created on 2020-07-11
# updated on 2023-06-01
