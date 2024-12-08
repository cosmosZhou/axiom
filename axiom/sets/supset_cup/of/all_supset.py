from util import *


@apply
def apply(imply):
    lhs, rhs = imply.of(Supset)
    expr, *limits = rhs.of(Cup)
    return All(Supset(lhs, expr).simplify(), *limits)


@prove
def prove(Eq):
    from Axiom import Sets
    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    x = Symbol(shape=(oo,), etype=dtype.complex[n])
    A = Symbol(etype=dtype.complex[n])

    Eq << apply(Supset(A, Cup[i:n](x[i])))

    Eq << Eq[1].reversed

    Eq << Sets.All_Subset.to.Subset.Cup.lhs.apply(Eq[-1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2020-09-13
