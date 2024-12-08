from util import *


@apply
def apply(given):
    A = given.of(Unequal[EmptySet])

    return GreaterEqual(Card(A), 1)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    A = Symbol(etype=dtype.integer)
    Eq << apply(Unequal(A, A.etype.emptySet))

    Eq << Sets.Ne_EmptySet.to.Gt_0.apply(Eq[0])

    Eq << ~Eq[1]

    Eq << GreaterEqual(Card(A), 0, plausible=True)

    Eq << Algebra.Cond.Any.to.Any.And.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.expr.apply(Sets.Lt.Ge.to.In.Range)


    Eq << Algebra.Any_Eq.Cond.to.Any.subs.apply(Eq[-1], Eq[2])




if __name__ == '__main__':
    run()

# created on 2020-07-12
# updated on 2023-05-26
