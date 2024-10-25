from util import *


@apply
def apply(ne, notin):
    _x, y = ne.of(Unequal)
    x, s = notin.of(NotElement)

    if x != _x:
        S[x], y = y, _x

    return NotElement(x, s | y.set)


@prove
def prove(Eq):
    from axiom import algebra, sets

    x, y = Symbol(integer=True, given=True)
    s = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Unequal(x, y), NotElement(x, s))

    Eq << algebra.iff.of.et.infer.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.apply(sets.ne.notin.then.notin)

    Eq << Eq[-1].this.rhs.apply(sets.ne.notin.of.notin)


if __name__ == '__main__':
    run()
# created on 2023-05-20
