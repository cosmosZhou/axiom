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

    Eq << ~Eq[-1]

    Eq << Eq[-1].this.args[0].apply(algebra.ou.then.ou.invert, pivot=1)

    Eq << Eq[-1].this.args[1].apply(algebra.ou.then.ou.invert, pivot=1)

    Eq << algebra.et.then.ou.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(And).apply(algebra.et.then.ou)

    Eq << Eq[-1].this.find(And).apply(algebra.gt_zero.lt_zero.then.lt_zero)

    Eq << algebra.cond.cond.then.cond.subs.apply(Eq[0], Eq[-1], invert=True)

    Eq << algebra.et.then.ou.apply(Eq[-1])

    Eq << Eq[-1].apply(algebra.lt_zero.gt_zero.then.lt_zero)

    Eq <<= Eq[-1] & Eq[0]





if __name__ == '__main__':
    run()
# created on 2023-04-15
# updated on 2023-05-12
