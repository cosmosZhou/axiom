from util import *


@apply
def apply(given, reverse=False):
    A, B = given.of(Equal[Intersection, EmptySet])
    if reverse:
        return Equal(B - A, B)

    return Equal(A - B, A)




@prove
def prove(Eq):
    from axiom import sets

    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Equal(A & B, A.etype.emptySet))

    Eq << Eq[0].apply(sets.eq.imply.eq.union, A - B).reversed


if __name__ == '__main__':
    run()

# created on 2019-01-31
