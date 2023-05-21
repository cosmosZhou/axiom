from util import *


@apply
def apply(given):
    x, y = given.of(Mul > 0)
    return Or((x < 0) & (y < 0), (x > 0) & (y > 0))


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(x * y > 0)

    Eq << ~Eq[-1]

    Eq << algebra.et.imply.ou.apply(Eq[-1], simplify=False)

    Eq << Eq[-1].this.args[1].apply(algebra.et.imply.ou)

    Eq << Eq[-1].this.find(And[Or]).apply(algebra.et.imply.ou)

    Eq << Eq[-1].this.find((Expr <= 0) & (Expr >= 0)).apply(algebra.le_zero.ge_zero.imply.le_zero)

    Eq << Eq[-1].this.find((Expr <= 0) & (Expr >= 0)).apply(algebra.ge_zero.le_zero.imply.le_zero)

    Eq << Eq[-1].this.args[0] * y

    Eq << Eq[-1].this.args[0] * x

    Eq <<= Eq[-1] & Eq[0]

    
    


if __name__ == '__main__':
    run()

# created on 2018-02-11

from . import split
# updated on 2023-05-13
