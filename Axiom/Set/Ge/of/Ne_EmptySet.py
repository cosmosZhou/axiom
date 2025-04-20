from util import *


@apply
def apply(given):
    A = given.of(Unequal[EmptySet])

    return GreaterEqual(Card(A), 1)


@prove
def prove(Eq):
    from Axiom import Set, Algebra

    A = Symbol(etype=dtype.integer)
    Eq << apply(Unequal(A, A.etype.emptySet))

    Eq << Set.Gt_0.of.Ne_EmptySet.apply(Eq[0])

    Eq << ~Eq[1]

    Eq << GreaterEqual(Card(A), 0, plausible=True)

    Eq << Algebra.Any.And.of.Cond.Any.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.expr.apply(Set.Mem.Range.of.Lt.Ge)


    Eq << Algebra.Any.of.Any_Eq.Cond.subs.apply(Eq[-1], Eq[2])




if __name__ == '__main__':
    run()

# created on 2020-07-12
# updated on 2023-05-26
