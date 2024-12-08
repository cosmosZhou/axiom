from util import *


@apply
def apply(contains1, contains2):
    e, A = contains1.of(Element)
    S[e], B = contains2.of(Element)

    return Element(e, A & B)


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    e = Symbol(integer=True)
    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Element(e, A), Element(e, B))

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Sets.In.In.to.In.Intersect)
    Eq << Eq[-1].this.rhs.apply(Sets.In.In.of.In.Intersect)


if __name__ == '__main__':
    run()
# created on 2023-08-26
