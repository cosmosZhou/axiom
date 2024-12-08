from util import *


@apply
def apply(lt, fx, x=None, left_open=True, right_open=True):
    m, M = lt.of(Less)
    p = fx.as_poly(x)
    assert p.degree() == 1
    a = p.nth(1)
    b = p.nth(0)
    y0 = a * m + b
    y1 = a * M + b

    return Equal(Sup[x:Interval(m, M, left_open=left_open, right_open=right_open)](fx), Max(y0, y1))


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    x, m, M, a, b, c = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(m < M, a * x + b, x)

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[-1], cond=a > 0)

    Eq <<= Algebra.Cond.Imply.of.And.Imply.And.apply(Eq[0], Eq[-2]), Algebra.Cond.of.And.Imply.split.apply(Eq[-1], cond=a < 0)

    Eq <<= Eq[-3].this.lhs.apply(Algebra.Gt_0.Lt.to.Sup.eq.Max.st.simple, a * x + b, x), Eq[-2].this.apply(Algebra.Imply.flatten), Eq[-1].this.apply(Algebra.Imply.flatten)

    Eq <<= Algebra.Cond.Imply.of.And.Imply.And.apply(Eq[0], Eq[-2]), Algebra.Imply.of.Imply.subs.apply(Eq[-1])

    Eq <<= Eq[-2].this.lhs.apply(Algebra.Lt_0.Lt.to.Sup.eq.Max.st.simple, a * x + b, x), Algebra.Imply.of.Cond.apply(Eq[-1])

    Eq <<= Eq[-1].this.find(Sup).simplify()

    Eq <<= Sets.Lt.to.Interval_Ne_EmptySet.apply(Eq[0])


if __name__ == '__main__':
    run()
# created on 2019-12-25
