from util import *


@apply
def apply(all_A, all_B):
    (x, B), (S[x], A) = all_A.of(All[Element])
    (S[x], S[A]), (S[x], S[B]) = all_B.of(All[Element])

    return Equal(A, B)


@prove
def prove(Eq):
    from Axiom import Sets
    n = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, shape=(n,))
    A, B = Symbol(etype=dtype.integer[n])

    Eq << apply(All[x:A](Element(x, B)), All[x:B](Element(x, A)))

    Eq << Sets.All_In.to.Subset.apply(Eq[0])

    Eq << Sets.All_In.to.Subset.apply(Eq[1])

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2018-04-27
