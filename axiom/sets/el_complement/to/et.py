from util import *


@apply
def apply(given):
    e, domain = given.of(Element)
    A, B = domain.of(Complement)

    return And(Element(e, A), NotElement(e, B))


@prove
def prove(Eq):
    from axiom import algebra, sets

    e = Symbol(integer=True, given=True)
    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Element(e, A - B))

    Eq << algebra.iff.of.et.infer.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(sets.el_complement.then.et)

    Eq << Eq[-1].this.rhs.apply(sets.el_complement.of.et, simplify=None)




if __name__ == '__main__':
    run()
# created on 2023-04-24
