from util import *


@apply
def apply(given):
    x, domain = given.of(Element)
    assert domain == FiniteSet(0, 1)

    return Equal(KroneckerDelta(0, x), 1 - x)


@prove
def prove(Eq):
    from Axiom import Algebra, Set, Logic

    x = Symbol(integer=True, given=True)
    given = Element(x, {0, 1})
    Eq << apply(given)

    Eq << Eq[-1].this.lhs.apply(Algebra.Delta.eq.Ite)

    Eq << Eq[-1].apply(Logic.Cond.given.Or.OrNot, cond=Equal(x, 0))

    Eq << Algebra.And.given.And.apply(Eq[-1])

    Eq <<= ~Eq[-1], ~Eq[-2]

    Eq << Eq[-2].apply(Algebra.Ne.of.Eq.Ne.subs)

    Eq << Eq[-1].apply(Algebra.Cond.of.Cond.Cond.subs, invert=True, reverse=True, ret=0)

    Eq << Eq[-1].apply(Set.NotMem.of.Ne.Ne, simplify=False)

    Eq <<= Eq[-1] & Eq[0]




if __name__ == '__main__':
    run()
# created on 2020-08-29
# updated on 2023-05-20
