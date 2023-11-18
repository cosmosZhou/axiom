from util import *


@apply
def apply(given):
    x, y = given.of(Mul >= 0)
    return Or(And(x >= 0, y >= 0), And(x <= 0, y <= 0))


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(x * y >= 0)

    Eq << Eq[1].this.args[1].apply(algebra.ge_zero.ge_zero.imply.ge_zero)

    Eq << Eq[-1].this.find(And).apply(algebra.le_zero.le_zero.imply.ge_zero)

    


if __name__ == '__main__':
    run()
# created on 2023-04-15
# updated on 2023-05-13
