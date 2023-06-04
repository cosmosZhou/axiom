from util import *


@apply
def apply(given, pivot=-1):
    A, U = given.of(Subset)
    args = U.of(Union)
    
    if isinstance(pivot, int):
        B = args[pivot]
    elif isinstance(pivot, slice):
        B = Union(*args[pivot])
    return Subset(A, B)


@prove
def prove(Eq):
    from axiom import sets

    A, B, C = Symbol(etype=dtype.integer)
    Eq << apply(Subset(A, B | C))

    Eq << sets.subset.imply.subset.union.rhs.apply(Eq[1], B)


if __name__ == '__main__':
    run()
# created on 2023-06-01
