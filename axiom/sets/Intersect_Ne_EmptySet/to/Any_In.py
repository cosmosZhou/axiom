from util import *


@apply
def apply(given, wrt=None, index=0):
    [*s] = given.of(Unequal[Intersection, EmptySet])

    A = s.pop(index)
    B = Intersection(*s)

    if wrt is None:
        wrt = B.element_symbol(A.free_symbols)

    return Any[wrt:B](Element(wrt, A))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Unequal(A & B, A.etype.emptySet))

    Eq << Sets.Eq_EmptySet.ou.Any_In.apply(A & B)

    Eq <<= Eq[-1] & Eq[0]

    Eq << Algebra.And.to.And.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(Sets.In_Intersect.to.And, simplify=None)

    Eq << Algebra.Any_And.to.Any.limits_absorb.apply(Eq[-1], index=1, simplify=None)


if __name__ == '__main__':
    run()

# created on 2018-09-07
