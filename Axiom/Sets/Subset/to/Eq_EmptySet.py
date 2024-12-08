from util import *


@apply
def apply(given):
    A, B = given.of(Subset)
    return Equal(A - B, A.etype.emptySet)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Subset(A, B))

    Eq << ~Eq[-1]

    Eq << Sets.Ne_EmptySet.to.Any_In.apply(Eq[-1], simplify=False)

    Eq << Eq[-1].this.expr.apply(Sets.In_Complement.to.And, simplify=None)

    Eq << Sets.Any_And.to.Any.single_variable.limits_absorb.apply(Eq[-1], index=0, simplify=None)

    Eq << Sets.Any.to.Any.limits.swap.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(Sets.In.Subset.to.In, Eq[0])

    Eq << Algebra.Any.to.Any.And.limits.single_variable.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-05-04
