from util import *


@apply
def apply(is_positive, z):
    r = is_positive.of(Expr > 0)
    return Equal(Arg(r * z), Arg(z))


@prove
def prove(Eq):
    from axiom import algebra

    z = Symbol(complex=True, given=True)
    r = Symbol(real=True)
    Eq << apply(r > 0, z)

    Eq << algebra.gt_zero.imply.any_eq.apply(Eq[0])

    Eq <<= Eq[2] & Eq[1]

    Eq << Eq[-1].this.apply(algebra.cond.any.given.any.et, simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.eq.eq.given.et.subs)




if __name__ == '__main__':
    run()
# created on 2018-08-25
# updated on 2023-05-20
