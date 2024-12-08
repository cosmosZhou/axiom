from util import *


@apply
def apply(given):
    e, domain = given.of(Element)
    A, B = domain.of(Complement)

    return And(Element(e, A), NotElement(e, B))


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    e = Symbol(integer=True, given=True)
    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Element(e, A - B))

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Sets.In_Complement.to.And)

    Eq << Eq[-1].this.rhs.apply(Sets.In_Complement.of.And, simplify=None)




if __name__ == '__main__':
    run()
# created on 2023-04-24
