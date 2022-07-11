from util import *


@apply
def apply(given):
    (fx, A), *limits = given.of(All[Subset])

    return Subset(Cup(fx, *limits).simplify(), A)


@prove
def prove(Eq):
    from axiom import sets
    n, m = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    x = Symbol(shape=(oo,), etype=dtype.complex * n)
    A = Symbol(etype=dtype.complex * n)

    Eq << apply(All[i:0:m](Subset(x[i], A)))

    Eq << sets.subset_cup.imply.all_subset.apply(Eq[1])


if __name__ == '__main__':
    run()

# created on 2020-07-29
