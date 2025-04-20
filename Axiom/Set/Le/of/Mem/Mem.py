from util import *


@apply
def apply(contains1, contains2):
    x, sx = contains1.of(Element)
    y, sy = contains2.of(Element)

    a, b = sx.of(Interval)
    _b, c = sy.of(Interval)
    assert b <= _b

    return LessEqual(x, y)


@prove
def prove(Eq):
    from Axiom import Set, Algebra

    a, b, c, x, y = Symbol(integer=True, given=True)
    Eq << apply(Element(x, Interval(a, b, left_open=True)), Element(y, Interval(b, c)))

    Eq << Set.And.of.Mem_Icc.apply(Eq[0])

    Eq << Set.And.of.Mem_Icc.apply(Eq[1])

    Eq << Algebra.Le.of.Le.Ge.apply(Eq[-3], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2020-05-09
