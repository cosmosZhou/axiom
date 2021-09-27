from util import *


@apply
def apply(imply):
    B, A = imply.of(Subset)
    return Equal(Complement(B, A), A.etype.emptySet)


@prove
def prove(Eq):
    from axiom import sets
    A, B = Symbol(etype=dtype.integer, given=True)

    Eq << apply(Subset(B, A))

    Eq << sets.is_empty.imply.subset.complement.apply(Eq[1])


if __name__ == '__main__':
    run()

