from util import *



@apply
def apply(a_less_than_x, x_less_than_b):
    A, X = a_less_than_x.of(Subset)
    _X, B = x_less_than_b.of(Subset)
    if X != _X:
        A, X, S[X], B = _X, B, A, X
    return Subset(A, B)


@prove
def prove(Eq):
    from Axiom import Sets
    A, X, B = Symbol(etype=dtype.complex)

    Eq << apply(Subset(A, X), Subset(X, B))

    Eq << Sets.Subset.to.All_In.apply(Eq[0])

    Eq << Eq[-1].this.expr.apply(Sets.In.Subset.to.In, Eq[1])

    Eq << Sets.All_In.to.Subset.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-04-20
