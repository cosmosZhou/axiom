from util import *


@apply
def apply(given, *limits):
    fx, A = given.of(Subset)

    return Subset(Cup(fx, *limits).simplify(), A)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra
    n, m = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    x = Symbol(shape=(oo,), etype=dtype.complex[n])
    A = Symbol(etype=dtype.complex[n])

    Eq << apply(Subset(x[i], A), (i, 0, m))

    Eq << Algebra.Cond.to.All.restrict.apply(Eq[0], (i, 0, m))

    Eq << Sets.All_Subset.to.Subset.Cup.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2020-08-03
