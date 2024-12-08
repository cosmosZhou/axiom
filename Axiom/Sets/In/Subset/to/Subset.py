from util import *


@apply
def apply(contains, subset):
    x, s = contains.of(Element)
    A, S[s] = subset.of(Subset)

    return Subset(A | {x}, s)


@prove
def prove(Eq):
    from Axiom import Sets
    n = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, shape=(n,), given=True)
    A = Symbol(etype=dtype.complex[n])
    B = Symbol(etype=dtype.complex[n], given=True)
    Eq << apply(Element(x, A), Subset(B, A))

    Eq << Sets.In.to.Subset.apply(Eq[0])

    Eq << Sets.Subset.Subset.to.Subset.Union.apply(Eq[-1], Eq[1])

if __name__ == '__main__':
    run()

# created on 2018-04-21
