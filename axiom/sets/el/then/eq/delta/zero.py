from util import *


@apply
def apply(given):
    x, domain = given.of(Element)
    assert domain == FiniteSet(0, 1)

    return Equal(KroneckerDelta(0, x), 1 - x)


@prove
def prove(Eq):
    from axiom import algebra, sets

    x = Symbol(integer=True, given=True)
    given = Element(x, {0, 1})
    Eq << apply(given)

    Eq << Eq[-1].this.lhs.apply(algebra.delta.to.piece)

    Eq << Eq[-1].apply(algebra.cond.of.et.ou, cond=Equal(x, 0))

    Eq << algebra.et.of.et.apply(Eq[-1])

    Eq <<= ~Eq[-1], ~Eq[-2]

    Eq << Eq[-2].apply(algebra.eq.ne.then.ne.subs)

    Eq << Eq[-1].apply(algebra.cond.cond.then.cond.subs, invert=True, reverse=True, ret=0)

    Eq << Eq[-1].apply(sets.ne.ne.then.notin, simplify=False)

    Eq <<= Eq[-1] & Eq[0]




if __name__ == '__main__':
    run()
# created on 2020-08-29
# updated on 2023-05-20
