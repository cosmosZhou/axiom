from util import *


@apply
def apply(lt_zero, ge_zero, lt, left_open=True, right_open=True, x=None):
    a = lt_zero.of(Expr > 0)
    m = ge_zero.of(Expr >= 0)
    S[m], M = lt.of(Less)
    if x is None:
        x = lt.generate_var(real=True)

    self = Inf[x:Interval(m, M, left_open=left_open, right_open=right_open)](x ** 2 * a)
    return Equal(self, m ** 2 * a)


@prove
def prove(Eq):
    from Axiom import Algebra

    a, m, M = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(a > 0, m >= 0, m < M, x=x)

    Eq << Algebra.Ge_0.Lt.to.Inf_Square.eq.Square.apply(Eq[1], Eq[2])

    Eq << Algebra.Gt_0.to.Inf.eq.Mul.apply(Eq[0], Eq[-1].lhs)

    Eq << Eq[-1].subs(Eq[-2])







if __name__ == '__main__':
    run()
# created on 2021-10-02
