from util import *


@apply
def apply(given):
    x = given.of(Unequal[0])
    return Unequal(~x, 0)


@prove
def prove(Eq):
    from axiom import algebra

    a = Symbol(complex=True, given=True)
    Eq << apply(Unequal(a, 0))

    Eq << ~Eq[1]


    Eq << algebra.conj_is_zero.then.is_zero.apply(Eq[-1])
    Eq << ~Eq[-1]



if __name__ == '__main__':
    run()
# created on 2023-05-02
