from util import *


@apply
def apply(given):
    expr, (x, A) = given.of(All)
    S[x], B = expr.of(Element)

    return Subset(A, B)


@prove
def prove(Eq):
    from axiom import sets
    n = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, shape=(n,))
    A, B = Symbol(etype=dtype.complex[n])

    Eq << apply(All[x:A](Element(x, B)))

    Eq << Eq[0].this.expr.apply(sets.el.then.subset, simplify=False)

    Eq << Eq[-1].apply(sets.all_subset.then.subset.cup.lhs)


if __name__ == '__main__':
    run()

# created on 2018-04-20
