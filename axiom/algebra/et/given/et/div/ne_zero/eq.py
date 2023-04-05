from util import *


@apply
def apply(given):
    (a, b), x = given.of(Equal & Unequal[0])
    return Unequal(x, 0), Equal((a / x).expand(), (b / x).expand()).simplify()


@prove
def prove(Eq):
    from axiom import algebra

    x, y, z = Symbol(integer=True)
    Eq << apply(Equal(x + y, z) & Unequal(x, 0))

    Eq << algebra.ne_zero.eq.imply.eq.mul.apply(Eq[1], Eq[2])

    Eq << algebra.et.given.et.apply(Eq[0])

    


if __name__ == '__main__':
    run()
# created on 2023-03-26
