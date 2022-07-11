from util import *


@apply
def apply(m_is_nonpositive, is_positive, lt, x=None):
    m = m_is_nonpositive.of(Expr <= 0)
    mM = is_positive.of(Expr > 0)
    M = mM - m

    U, M2 = lt.of(Less)
    _M = M2.of(Expr ** 2)
    assert _M == M
    if x is None:
        x = lt.generate_var(real=True)
    return Any[x:Interval(m, M, left_open=True, right_open=True)](x ** 2 > U)


@prove
def prove(Eq):
    from axiom import algebra, sets

    m, M, U = Symbol(real=True, given=True)
    Eq << apply(m <= 0, m + M > 0, U < M ** 2)

    Eq << -Eq[0]

    Eq << Eq[1].this.apply(algebra.gt.transport).reversed

    Eq << algebra.ge_zero.lt.lt.imply.any_gt.square.apply(Eq[-2], Eq[-1], Eq[2])

    Eq << sets.le_zero.imply.subset.interval.upper.apply(Eq[0], M, left_open=True, right_open=True)

    Eq << sets.subset.any.imply.any.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2019-09-07
