from util import *


@apply
def apply(self, simplify=True):
    from axiom.sets.el_union.imply.ou import split
    return split(self, simplify=simplify)


@prove
def prove(Eq):
    from axiom import algebra, sets

    e = Symbol(integer=True, given=True)
    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Element(e, A | B))

    Eq << algebra.iff.given.et.infer.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(sets.el_union.imply.ou)
    Eq << Eq[-1].this.rhs.apply(sets.el_union.given.ou)

    


if __name__ == '__main__':
    run()
# created on 2023-04-18
