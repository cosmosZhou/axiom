from util import *


@apply
def apply(is_negative, lt, fx, x=None, left_open=True, right_open=True):    
    m, M = lt.of(Less)
    a = is_negative.of(Expr < 0)    
    p = fx.as_poly(x)
    assert p.degree() == 1
    assert a == p.nth(1)
    b = p.nth(0)
            
    return Equal(Sup[x:Interval(m, M, left_open=left_open, right_open=right_open)](fx), Max(a * m + b, a * M + b))


@prove
def prove(Eq):
    from axiom import algebra

    m, M, x, a, b = Symbol(real=True, given=True)
    Eq << apply(a < 0, m < M, a * x + b, x)

    Eq << algebra.is_negative.lt.imply.gt.mul.apply(Eq[0], Eq[1])

    Eq << algebra.gt.imply.eq.max.apply(Eq[-1]) + b

    Eq << Eq[-1].this.lhs.apply(algebra.add.to.max)

    Eq << algebra.is_negative.lt.imply.eq.sup.st.simple.apply(Eq[0], Eq[1], a * x + b, x)

    Eq << Eq[-1].subs(Eq[-2].reversed)


if __name__ == '__main__':
    run()