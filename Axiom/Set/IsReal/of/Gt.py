from util import *


@apply
def apply(given):
    n, b = given.of(Greater)
    assert n.is_finite
    return Element(n, Interval(-oo, oo))


@prove
def prove(Eq):
    from Axiom import Set

    x = Symbol(complex=True, given=True)
    b = Symbol(real=True, given=True)
    Eq << apply(x > b)

    Eq << Set.Mem.Icc.of.Gt.apply(Eq[0])

    Eq << Set.Mem_Union.of.Mem.apply(Eq[-1], Interval(-oo, oo), simplify=None)


if __name__ == '__main__':
    run()
# created on 2020-04-02
