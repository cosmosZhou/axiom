from util import *


@apply
def apply(ne, NotIn):
    _x, y = ne.of(Unequal)
    x, s = NotIn.of(NotElement)

    if x != _x:
        S[x], y = y, _x

    return NotElement(x, s | y.set)


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    x, y = Symbol(integer=True, given=True)
    s = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Unequal(x, y), NotElement(x, s))

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.apply(Sets.Ne.NotIn.to.NotIn)

    Eq << Eq[-1].this.rhs.apply(Sets.Ne.NotIn.of.NotIn)


if __name__ == '__main__':
    run()
# created on 2023-05-20
