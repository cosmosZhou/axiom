from util import *


@apply
def apply(is_positive_x, is_nonpositive_y):
    x = is_positive_x.of(Expr > 0)
    y = is_nonpositive_y.of(Expr <= 0)
    return LessEqual(x * y, 0)


@prove
def prove(Eq):
    from Axiom import Algebra
    x, y = Symbol(real=True)

    Eq << apply(x > 0, y <= 0)

    Eq.case0 = Imply(Equal(y, 0), Eq[-1], plausible=True)

    Eq << Eq.case0.this.apply(Algebra.Imply.subs)

    Eq << Algebra.Cond.to.Imply.apply(Eq[0], cond=y < 0)

    Eq << Algebra.Imply_And.to.Imply.And.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Gt_0.Lt_0.to.Lt_0)

    Eq << Eq[-1].this.rhs.apply(Algebra.Lt_0.to.Le_0)

    Eq <<= Eq.case0 & Eq[-1]

    Eq << Algebra.Cond.Imply.to.Cond.trans.apply(Eq[1], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-02-08
