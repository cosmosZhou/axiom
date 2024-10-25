from util import *


@apply
def apply(given):
    x = given.of(Expr > 0)
    return Equal(sign(x), 1)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(complex=True)
    Eq << apply(x > 0)

    Eq << algebra.gt_zero.then.eq.abs.apply(Eq[0])

    Eq << Eq[1].lhs.this.apply(algebra.sign.to.piece.abs)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << algebra.cond_piece.then.infer.apply(Eq[-1], 1)

    Eq << algebra.gt_zero.then.ne_zero.apply(Eq[0])

    Eq << algebra.cond.infer.then.cond.trans.apply(Eq[-1], Eq[-2])




if __name__ == '__main__':
    run()
# created on 2023-05-29
# updated on 2023-06-06
