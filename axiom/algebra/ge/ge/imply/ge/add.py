from util import *



@apply
def apply(a_less_than_x, x_less_than_b):
    a, x = a_less_than_x.of(GreaterEqual)
    b, y = x_less_than_b.of(GreaterEqual)

    return GreaterEqual(a + b, x + y)


@prove
def prove(Eq):
    from axiom import algebra
    a, x, b, y = Symbol(real=True)

    Eq << apply(a >= x, y >= b)

    Eq << Eq[0] + y

    Eq << Eq[1] + x

    Eq << algebra.ge.ge.imply.ge.transit.apply(Eq[-2], Eq[-1])



if __name__ == '__main__':
    run()
