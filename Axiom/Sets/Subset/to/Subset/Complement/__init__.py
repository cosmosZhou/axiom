from util import *


@apply
def apply(given, S):
    lhs, rhs = given.of(Subset)
    return Subset(lhs - S, rhs - S)

@prove
def prove(Eq):
    from Axiom import Sets

    n = Symbol(integer=True, positive=True)
    A, B, S = Symbol(etype=dtype.complex[n])
    Eq << apply(Subset(A, B), S)



    C = Symbol(A - S)
    Eq << C.this.definition

    V = Symbol(B - S)
    Eq << V.this.definition

    # Eq << Sets.Subset.then.Subset.intersection.apply(Eq[-1], V, simplify=None)
    Eq << Sets.Subset.to.Eq.Intersect.apply(Eq[0])

    Eq <<= (C & V).this.subs(C.this.definition, V.this.definition)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[-1].subs(C.this.definition.reversed)

    Eq << Sets.Eq_Intersect.to.Subset.apply(Eq[-1])

    Eq << Eq[-1].subs(C.this.definition, V.this.definition)


if __name__ == '__main__':
    run()
# created on 2020-11-21
from . import lhs