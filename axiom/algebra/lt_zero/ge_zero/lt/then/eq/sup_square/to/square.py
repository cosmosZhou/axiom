from util import *


@apply
def apply(lt_zero, ge_zero, lt, left_open=True, right_open=True, x=None):
    a = lt_zero.of(Expr < 0)
    m = ge_zero.of(Expr >= 0)
    S[m], M = lt.of(Less)
    if x is None:
        x = lt.generate_var(real=True)

    self = Sup[x:Interval(m, M, left_open=left_open, right_open=right_open)](x ** 2 * a)
    return Equal(self, m ** 2 * a)


@prove
def prove(Eq):
    from axiom import algebra

    a, m, M = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(a < 0, m >= 0, m < M, x=x)

    Eq << algebra.ge_zero.lt.then.eq.inf_square.to.square.apply(Eq[1], Eq[2])

    Eq << algebra.lt_zero.then.eq.inf.to.mul.sup.apply(Eq[0], Eq[-1].lhs, div=True)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1] * a





if __name__ == '__main__':
    run()
# created on 2021-10-02
