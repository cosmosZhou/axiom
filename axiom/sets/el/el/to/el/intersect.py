from util import *


@apply
def apply(contains1, contains2):
    e, A = contains1.of(Element)
    S[e], B = contains2.of(Element)

    return Element(e, A & B)


@prove
def prove(Eq):
    from axiom import algebra, sets

    e = Symbol(integer=True)
    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Element(e, A), Element(e, B))

    Eq << algebra.iff.given.et.infer.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(sets.el.el.imply.el.intersect)
    Eq << Eq[-1].this.rhs.apply(sets.el.el.given.el.intersect)


if __name__ == '__main__':
    run()
# created on 2023-08-26
