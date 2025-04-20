from util import *


@apply
def apply(contains1, contains2):
    e, A = contains1.of(Element)
    S[e], B = contains2.of(Element)

    return Element(e, A & B)


@prove
def prove(Eq):
    from Axiom import Algebra, Set, Logic

    e = Symbol(integer=True)
    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Element(e, A), Element(e, B))

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Set.Mem.Inter.of.Mem.Mem)
    Eq << Eq[-1].this.rhs.apply(Set.Mem.Mem.given.Mem.Inter)


if __name__ == '__main__':
    run()
# created on 2023-08-26
