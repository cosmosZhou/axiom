from util import *


@apply
def apply(imply):
    B, A = imply.of(Subset)
    return Equal(Complement(B, A), A.etype.emptySet)


@prove
def prove(Eq):
    from Axiom import Sets
    A, B = Symbol(etype=dtype.integer, given=True)

    Eq << apply(Subset(B, A))

    Eq << Sets.Eq_EmptySet.to.Subset.Complement.apply(Eq[1])


if __name__ == '__main__':
    run()

# created on 2018-03-04
