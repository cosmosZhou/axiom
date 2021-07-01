from util import *



@apply
def apply(*given):
    x_less_than_y, a_less_than_b = given
    x, y = x_less_than_y.of(Greater)
    a, b = a_less_than_b.of(Greater)
    return Greater(Max(x, a), Max(y, b))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)

    a = Symbol.a(real=True)
    b = Symbol.b(real=True)

    Eq << apply(x > y, a > b)

    Eq << GreaterEqual(Max(x, a), x, plausible=True)

    Eq << algebra.ge.gt.imply.gt.transit.apply(Eq[-1], Eq[0])

    Eq << GreaterEqual(Max(x, a), a, plausible=True)

    Eq << algebra.gt.ge.imply.gt.transit.apply(Eq[1], Eq[-1])

    Eq << algebra.gt.gt.imply.gt.max.rhs.apply(Eq[-1], Eq[-3])

if __name__ == '__main__':
    run()