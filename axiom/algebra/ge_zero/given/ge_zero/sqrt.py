from util import *


@apply
def apply(given):
    x = given.of(Expr >= 0)
    return sqrt(x) >= 0


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True)
    Eq << apply(x >= 0)

    Eq << algebra.ge_zero.ge_zero.imply.ge_zero.apply(Eq[1], Eq[1])

    


if __name__ == '__main__':
    run()
# created on 2023-06-20
