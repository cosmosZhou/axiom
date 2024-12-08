from util import *


@apply
def apply(given, wrt=None):
    AB = given.of(Unequal[EmptySet])

    A, B = AB.of(Complement)
    if wrt is None:
        wrt = A.element_symbol(B.free_symbols)
    assert wrt.type == B.etype
    return Any[wrt:A](Element(wrt, AB))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Unequal(A - B, A.etype.emptySet))

    Eq << Sets.Ne_EmptySet.to.Any_In.apply(Eq[0])

    i = Eq[-1].variable
    Eq << Imply(Element(i, A - B), And(Element(i, A - B), Element(i, A)), plausible=True)

    Eq << Algebra.Imply.of.And.Imply.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Sets.In.to.In.st.Complement)

    Eq << Eq[2].this.expr.apply(Algebra.Cond.Imply.to.Cond.trans, Eq[-2], simplify=None)

    Eq << Eq[-1].apply(Algebra.Any_And.to.Any.limits_absorb, index=0, simplify=None)


if __name__ == '__main__':
    run()

# created on 2018-03-24
