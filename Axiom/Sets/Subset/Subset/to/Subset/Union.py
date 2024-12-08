from util import *



@apply
def apply(subset_ab, subset_xy):
    a, b = subset_ab.of(Subset)
    x, y = subset_xy.of(Subset)

    return Subset(a | x, b | y)


@prove
def prove(Eq):
    from Axiom import Sets
    A, B, X, Y = Symbol(etype=dtype.integer)

    Eq << apply(Subset(A, B), Subset(X, Y))

    Eq << Sets.Subset.to.Subset.Union.rhs.apply(Eq[0], Y)

    Eq << Sets.Subset.to.Subset.Union.rhs.apply(Eq[1], B)

    Eq <<= Eq[-1] & Eq[-2]

if __name__ == '__main__':
    run()

# created on 2018-04-21
