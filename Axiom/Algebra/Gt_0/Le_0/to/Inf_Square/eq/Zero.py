from util import *


@apply
def apply(is_positive, is_nonpositive, left_open=True, right_open=True, x=None):
    M = is_positive.of(Expr > 0)
    m = is_nonpositive.of(Expr <= 0)
    if x is None:
        x = m.generate_var(M.free_symbols, real=True)

    self = Inf[x:Interval(m, M, left_open=left_open, right_open=right_open)](x ** 2)
    return Equal(self, 0)


@prove
def prove(Eq):
    from Axiom import Algebra

    m, M = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(M > 0, m <= 0, x=x)

    Eq << Algebra.Cond.to.Imply.And.apply(Eq[0], cond=m < 0)

    Eq << Eq[-1].this.rhs.apply(Algebra.Gt_0.Lt_0.to.Inf_Square.eq.Zero)

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[2], cond=m < 0)

    Eq << Algebra.Cond.to.Imply.And.apply(Eq[0] & Eq[1], cond=m >= 0)

    Eq << Eq[-1].this.rhs.args[1:].apply(Algebra.Le.Ge.to.Eq)

    Eq << Eq[-1].this.find(Greater).apply(Algebra.Gt_0.to.Inf_Square.eq.Zero)

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.Eq.to.Eq.subs.lhs, reverse=True)




if __name__ == '__main__':
    run()
# created on 2019-08-25
# updated on 2023-05-20
