from util import *


@apply
def apply(self, simplify=True):
    from Axiom.Sets.In_Union.to.Or import split
    return split(self, simplify=simplify)


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    e = Symbol(integer=True, given=True)
    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Element(e, A | B))

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Sets.In_Union.to.Or)
    Eq << Eq[-1].this.rhs.apply(Sets.In_Union.of.Or)




if __name__ == '__main__':
    run()
# created on 2023-04-18
