from util import *


@apply
def apply(a_less_than_x, x_less_than_b):
    A, X = a_less_than_x.of(Subset)
    B, _X = x_less_than_b.of(Supset)
    if X != _X:
        A, X, S[X], B = _X, B, A, X
    return Subset(A, B)


@prove
def prove(Eq):
    from axiom import sets
    A, X, B = Symbol(etype=dtype.complex)

    Eq << apply(Subset(A, X), Supset(B, X))

    Eq << Eq[1].reversed

    Eq << sets.subset.subset.then.subset.trans.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()
# created on 2021-06-29
