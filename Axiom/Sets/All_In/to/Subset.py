from util import *


@apply
def apply(given):
    expr, (x, A) = given.of(All)
    S[x], B = expr.of(Element)

    return Subset(A, B)


@prove
def prove(Eq):
    from Axiom import Sets
    n = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, shape=(n,))
    A, B = Symbol(etype=dtype.complex[n])

    Eq << apply(All[x:A](Element(x, B)))

    Eq << Eq[0].this.expr.apply(Sets.In.to.Subset, simplify=False)

    Eq << Eq[-1].apply(Sets.All_Subset.to.Subset.Cup.lhs)


if __name__ == '__main__':
    run()

# created on 2018-04-20
