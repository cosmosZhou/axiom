from util import *


@apply
def apply(is_negative, lt, fx, x=None, left_open=True, right_open=True):
    m, M = lt.of(Less)
    a = is_negative.of(Expr < 0)
    p = fx.as_poly(x)
    assert p.degree() == 1
    assert a == p.nth(1)
    b = p.nth(0)

    return Equal(Sup[x:Interval(m, M, left_open=left_open, right_open=right_open)](fx), a * m + b)


@prove
def prove(Eq):
    from axiom import algebra

    m, M, x, a, b = Symbol(real=True, given=True)
    Eq << apply(a < 0, m < M, a * x + b, x)

    Eq << Eq[-1].this.lhs.apply(algebra.sup.to.add)

    Eq << algebra.lt_zero.imply.eq.sup.to.mul.inf.apply(Eq[0], Eq[-1].lhs)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << algebra.eq.given.eq.div.apply(Eq[-1], a)
    Eq << algebra.lt.imply.eq.inf.apply(Eq[1], x)


if __name__ == '__main__':
    run()
# created on 2019-12-23
# updated on 2019-12-23
