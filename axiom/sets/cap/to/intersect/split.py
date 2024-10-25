from util import *


@apply
def apply(self, indices, wrt=None, *, simplify=True):
    from axiom.algebra.sum.to.add.split import split
    return Equal(self, split(Cap, self, indices, wrt=wrt, simplify=simplify))


@prove(provable=False)
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(integer=True)
    f = Function(etype=dtype.real)
    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Cap[x:A](f(x)), B)

    return # the following will result recursive proving
    Eq << sets.eq.of.suffice.apply(Eq[0], wrt='y')
    Eq <<= Eq[-2].this.rhs.apply(sets.element.of.contains.split.intersection, simplify=False), \
    Eq[-1].this.lhs.apply(sets.element.then.contains.split.intersection)
    Eq <<= Eq[-2].this.lhs.apply(sets.element.then.all_contains.st.cap), \
    Eq[-1].this.rhs.apply(sets.element.of.all_contains.st.cap)
    Eq <<= Eq[-2].this.rhs.args[0].apply(sets.element.of.all_contains.st.cap), \
    Eq[-1].this.lhs.args[0].apply(sets.element.then.all_contains.st.cap)
    Eq <<= Eq[-2].this.rhs.args[0].apply(sets.element.of.all_contains.st.cap), \
    Eq[-1].this.lhs.args[0].apply(sets.element.then.all_contains.st.cap)
    Eq <<= Eq[-2].this.rhs.apply(algebra.all.all.of.all.limits_union), \
    Eq[-1].this.lhs.apply(algebra.all.all.then.all.limits_union)


if __name__ == '__main__':
    run()

# created on 2021-01-19
