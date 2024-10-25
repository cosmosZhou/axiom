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
    from axiom import sets

    x, y = Symbol(integer=True, given=True)
    s = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Unequal(x, y), NotElement(x, s))

    Eq << sets.ne.of.notin.apply(Eq[0], simplify=False)

    Eq <<= Eq[-1] & Eq[1]




if __name__ == '__main__':
    run()
# created on 2023-05-20
