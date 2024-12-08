from util import *


@apply
def apply(contains1, contains2, w=None):
    x0, s = contains1.of(Element)
    x1, S[s] = contains2.of(Element)
    assert s.is_Interval

    assert 0 <= w <= 1
    return Element(x0 * w + x1 * (1 - w), s)


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    a, b, x0, x1 = Symbol(real=True)
    domain = Interval(a, b, left_open=True)
    w = Symbol(domain=Interval(0, 1))
    Eq << apply(Element(x0, domain), Element(x1, domain), w)

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[-1], cond=w > 0)

    Eq << (w <= 0).this.apply(Algebra.Le.to.Eq.squeeze.Interval)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.Cond.of.And.subs)

    Eq << Algebra.Imply.of.And.Imply.apply(Eq[-1])

    Eq << Algebra.Cond.to.Imply.apply(Eq[1], cond=w<=0)

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[3], cond=w < 1)

    Eq.open_Interval, Eq.ge = Eq[-2].this.apply(Algebra.Imply.flatten), Eq[-1].this.apply(Algebra.Imply.flatten)

    Eq << (w >= 1).this.apply(Algebra.Ge.to.Eq.squeeze)

    Eq <<= Eq[-1] & Eq.ge

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.Cond.of.And.subs)

    Eq << Algebra.Imply.of.And.Imply.apply(Eq[-1])

    Eq << Algebra.Cond.to.Imply.apply(Eq[0], cond=w >= 1)

    Eq << Eq.open_Interval.this.lhs.apply(Sets.Lt.Gt.to.In.Interval, simplify=None)

    Eq << Algebra.Cond.to.Imply.apply(Eq[0] & Eq[1], cond=Eq[-1].lhs)

    Eq << Algebra.Imply_And.to.Imply.And.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Sets.In.In.In.to.In.Interval.open)





if __name__ == '__main__':
    run()

# created on 2020-05-08
# updated on 2023-08-26
