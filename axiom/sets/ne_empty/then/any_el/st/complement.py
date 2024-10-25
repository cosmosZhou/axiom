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
    from axiom import sets, algebra

    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Unequal(A - B, A.etype.emptySet))

    Eq << sets.ne_empty.then.any_el.apply(Eq[0])

    i = Eq[-1].variable
    Eq << Infer(Element(i, A - B), And(Element(i, A - B), Element(i, A)), plausible=True)

    Eq << algebra.infer.of.et.infer.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(sets.el.then.el.st.complement)

    Eq << Eq[2].this.expr.apply(algebra.cond.infer.then.cond.trans, Eq[-2], simplify=None)

    Eq << Eq[-1].apply(algebra.any_et.then.any.limits_absorb, index=0, simplify=None)


if __name__ == '__main__':
    run()

# created on 2018-03-24
