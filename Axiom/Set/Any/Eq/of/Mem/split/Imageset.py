from util import *


@apply(simplify=False)
def apply(given):
    y, (expr, (x, base_set)) = given.of(Element[Cup[FiniteSet]])
    return Any[x:base_set](Equal(y, expr))


@prove
def prove(Eq):
    from Axiom import Set
    y = Symbol(integer=True, given=True)
    x = Symbol(integer=True)
    f = Function(integer=True)

    S = Symbol(etype=dtype.integer, given=True)

    Eq << apply(Element(y, imageset(x, f(x), S)))

    Eq << ~Eq[1]

    Eq << Eq[-1].this.expr.apply(Set.NotMem.of.Ne)

    Eq << Set.NotMem.of.All_NotMem.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

# created on 2020-08-12
