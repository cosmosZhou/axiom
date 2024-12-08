from util import *


@apply
def apply(given):
    abs_x, a = given.of(Less)
    x = abs_x.of(Abs)
    assert x.is_extended_real
    return Element(x, Interval(-a, a, left_open=True, right_open=True))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x, a = Symbol(real=True, given=True)
    Eq << apply(abs(x) < a)

    Eq << Sets.In_Interval.to.And.apply(Eq[1])
    Eq << Algebra.Lt.Gt.to.Lt.Abs.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2020-04-24
