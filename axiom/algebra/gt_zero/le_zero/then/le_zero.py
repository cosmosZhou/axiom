from util import *


@apply
def apply(is_positive_x, is_nonpositive_y):
    x = is_positive_x.of(Expr > 0)
    y = is_nonpositive_y.of(Expr <= 0)
    return LessEqual(x * y, 0)


@prove
def prove(Eq):
    from axiom import algebra
    x, y = Symbol(real=True)

    Eq << apply(x > 0, y <= 0)

    Eq.case0 = Infer(Equal(y, 0), Eq[-1], plausible=True)

    Eq << Eq.case0.this.apply(algebra.infer.subs)

    Eq << algebra.cond.then.infer.apply(Eq[0], cond=y < 0)

    Eq << algebra.infer_et.then.infer.et.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.gt_zero.lt_zero.then.lt_zero)

    Eq << Eq[-1].this.rhs.apply(algebra.lt_zero.then.le_zero)

    Eq <<= Eq.case0 & Eq[-1]

    Eq << algebra.cond.infer.then.cond.trans.apply(Eq[1], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-02-08
