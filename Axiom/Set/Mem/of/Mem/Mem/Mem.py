from util import *


@apply
def apply(contains_x, contains_y, contains_z):
    x, interval_x = contains_x.of(Element)
    a, b = interval_x.of(Interval)
    left_open = interval_x.left_open

    y, interval_y = contains_y.of(Element)
    c, d = interval_y.of(Interval)
    right_open = interval_y.right_open

    z, interval_z = contains_z.of(Element)
    S[x], S[y] = interval_z.of(Interval)

    return Element(z, Interval(a, d, left_open=left_open, right_open=right_open))

@prove
def prove(Eq):
    from Axiom import Set, Algebra

    a, b, c, d, x, y, z = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b, left_open=True)), Element(y, Interval(c, d, right_open=True)), Element(z, Interval(x, y, left_open=True)))

    Eq << Set.Mem_Icc.given.And.apply(Eq[-1])

    Eq << Set.And.of.Mem_Icc.apply(Eq[2])

    Eq <<= Set.Gt.of.Mem_Icc.apply(Eq[0]), Set.Lt.of.Mem_Icc.apply(Eq[1])

    Eq << Algebra.Gt.of.Gt.Gt.apply(Eq[-4], Eq[-2])

    Eq << Algebra.Lt.of.Le.Lt.apply(Eq[-3], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-02-24

