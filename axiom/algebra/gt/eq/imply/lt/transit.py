from util import *


@apply
def apply(b_greater_than_x, x_eq_a):
    b, x = b_greater_than_x.of(Greater)
    _x, a = x_eq_a.of(Equal)
    assert x == _x
    return Less(a, b)


@prove
def prove(Eq):
    from axiom import algebra
    a, x, b = Symbol(real=True)

    Eq << apply(b > x, Equal(x, a))

    Eq << algebra.gt.eq.imply.gt.transit.apply(Eq[0], Eq[1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2019-07-12
