from util import *


@apply
def apply(given, divisor=None):
    (x, y), z = given.of(Abs[Expr * Expr] < Expr)
    if divisor is None:
        divisor = sqrt(z)
        dividend = divisor
    else:
        assert divisor > 0
        dividend = z / divisor
    
    return Abs(x) < divisor, Abs(y) < dividend


@prove
def prove(Eq):
    from axiom import algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(Abs(x * y) < z)

    Eq << algebra.lt.lt.imply.lt.abs.mul.apply(Eq[1], Eq[2])

    


if __name__ == '__main__':
    run()
# created on 2023-04-15
