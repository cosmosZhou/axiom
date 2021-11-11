from util import *


@apply
def apply(is_negative, lt, fx, x=None, left_open=True, right_open=True):
    m, M = lt.of(Less)
    a = is_negative.of(Expr < 0)
    p = fx.as_poly(x)
    assert p.degree() == 1
    assert a == p.nth(1)
    b = p.nth(0)

    return Equal(Inf[x:Interval(m, M, left_open=left_open, right_open=right_open)](fx), a * M + b)


@prove
def prove(Eq):
    from axiom import algebra

    m, M, a, b = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(a < 0, m < M, a * x + b, x)

    Eq << Eq[-1].this.lhs.apply(algebra.inf.to.add)

    Eq << algebra.lt_zero.imply.lt_zero.div.apply(Eq[0])

    Eq << algebra.lt_zero.imply.eq.inf.to.mul.sup.apply(Eq[0], Eq[-2].lhs)

    Eq << Eq[-3].subs(Eq[-1])

    Eq << algebra.eq.given.eq.div.apply(Eq[-1], a)

    Eq << algebra.lt.imply.eq.sup.apply(Eq[1], x)












if __name__ == '__main__':
    run()
# created on 2020-01-22
# updated on 2020-01-22
