from util import *


@apply
def apply(given):
    x_in_A, x_in_B = given.of(Infer)

    x, A = x_in_A.of(Subset)
    S[x], B = x_in_B.of(Subset)
    return Subset(A, B)


@prove
def prove(Eq):
    from axiom import sets

    n = Symbol(integer=True, positive=True)
    A, B = Symbol(etype=dtype.integer * n)
    X = Symbol(etype=dtype.integer * n, given=True)
    Eq << apply(Infer(Subset(X, A), Subset(X, B)))

    Eq << sets.subset.imply.infer.subset.apply(Eq[1], X)

    

    

    


if __name__ == '__main__':
    run()
# created on 2022-09-20
