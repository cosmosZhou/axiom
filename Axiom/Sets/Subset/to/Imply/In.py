from util import *


@apply
def apply(given, x):
    A, B = given.of(Subset)
    return Imply(Element(x, A), Element(x, B))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    n = Symbol(integer=True, positive=True)
    A, B = Symbol(etype=dtype.integer[n])
    x = Symbol(complex=True, shape=(n,), given=True)
    Eq << apply(Subset(A, B), x)

    Eq << Sets.Subset.to.All_In.apply(Eq[0])

    a = Eq[-1].variable
    Eq << Algebra.All.to.Imply.apply(Eq[-1])

    Eq << Eq[-1].subs(a, x)




if __name__ == '__main__':
    run()
# created on 2022-09-20
