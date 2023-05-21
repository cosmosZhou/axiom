from util import *


@apply
def apply(given, swap=False):
    x, y = given.of(Mul <= 0)
    if swap:
        return x <= 0, y >= 0
    else:
        return x >= 0, y <= 0


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(x * y <= 0)

    Eq << algebra.ge_zero.le_zero.imply.le_zero.apply(*Eq[1:])

    


if __name__ == '__main__':
    run()
# created on 2023-04-15
