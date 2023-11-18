from util import *


@apply
def apply(given):
    x = given.of(Unequal[0])
    return Unequal(abs(x), 0)


@prove
def prove(Eq):
    from axiom import algebra

    a = Symbol(complex=True, given=True)
    Eq << apply(Unequal(a, 0))

    Eq << ~Eq[1]

    Eq << algebra.abs_is_zero.imply.is_zero.apply(Eq[-1])
    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2018-03-17
