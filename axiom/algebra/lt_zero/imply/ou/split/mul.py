from util import *


@apply
def apply(given):
    x, y = given.of(Mul < 0)
    return Or(And(x > 0, y < 0), And(x < 0, y > 0))


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(x * y < 0)

    Eq << ~Eq[-1]

    Eq << Eq[-1].this.args[0].apply(algebra.ou.imply.ou.invert, pivot=1)

    Eq << Eq[-1].this.find(Or).apply(algebra.ou.imply.ou.invert, pivot=0)

    Eq << algebra.et.imply.ou.apply(Eq[-1], 1, simplify=None)

    Eq << Eq[-1].this.find(And).apply(algebra.et.imply.ou, 1)

    Eq << Eq[-1].this.find((Expr > 0) & (Expr >= 0)).apply(algebra.ge_zero.gt_zero.imply.ge_zero)

    Eq << Eq[-1].this.find((Expr > 0) & (Expr >= 0)).apply(algebra.ge_zero.gt_zero.imply.ge_zero)

    Eq << Eq[-1].this.find(And).args[:2].apply(algebra.le_zero.lt_zero.imply.ge_zero)

    Eq << algebra.cond.cond.imply.cond.subs.apply(Eq[0], Eq[-1], invert=True)

    Eq << Eq[0].subs(Eq[-1])

    
    


if __name__ == '__main__':
    run()
# created on 2023-04-15
# updated on 2023-05-13
