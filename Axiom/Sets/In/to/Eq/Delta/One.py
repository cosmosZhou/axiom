from util import *


@apply
def apply(given):
    x, domain = given.of(Element)
    assert domain == FiniteSet(0, 1)

    return Equal(KroneckerDelta(1, x), x)


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    x = Symbol(integer=True, given=True)
    given = Element(x, {0, 1})
    Eq << apply(given)

    Eq << Eq[-1].this.lhs.apply(Algebra.Delta.eq.Piece)

    Eq << Eq[-1].apply(Algebra.Cond.of.And.Or, cond=Equal(1, x))

    Eq << Algebra.And.of.And.apply(Eq[-1])

    Eq <<= ~Eq[-1], ~Eq[-2]

    Eq << Eq[-2].apply(Algebra.Eq.Ne.to.Ne.subs)

    Eq << Eq[-1].apply(Algebra.Cond.Cond.to.Cond.subs, invert=True, ret=0)

    Eq << Eq[-1].apply(Sets.Ne.Ne.to.NotIn, simplify=False)

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

# created on 2021-03-09