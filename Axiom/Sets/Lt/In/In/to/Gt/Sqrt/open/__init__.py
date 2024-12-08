from util import *


@apply
def apply(lt, contains, contains_y):
    x, domain_x = contains.of(Element)
    y, domain_y = contains_y.of(Element)
    assert domain_x in Interval(-1, 1, left_open=True, right_open=True)
    assert domain_y in Interval(-1, 1, left_open=True, right_open=True)
    S[x], S[y] = lt.of(Less)
    return y * sqrt(1 - x ** 2) > x * sqrt(1 - y ** 2)


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    x, y = Symbol(real=True)
    Eq << apply(x < y, Element(x, Interval(-1, 1, left_open=True, right_open=True)), Element(y, Interval(-1, 1, left_open=True, right_open=True)))

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[-1], cond=y > 0)

    Eq <<= Algebra.Cond.of.And.Imply.split.apply(Eq[-2], cond=x > 0), Algebra.Cond.of.And.Imply.split.apply(Eq[-1], cond=x > 0)

    Eq.gt_gt, Eq.le_gt, Eq.gt_le, Eq.le_le = Eq[-4].this.apply(Algebra.Imply.flatten), Eq[-3].this.apply(Algebra.Imply.flatten), Eq[-2].this.apply(Algebra.Imply.flatten), Eq[-1].this.apply(Algebra.Imply.flatten)

    Eq << Sets.In.to.Gt_.Sqrt.Zero.apply(Eq[2])

    Eq << Algebra.Cond.to.Imply.And.apply(Eq[-1], cond=x <= 0)

    Eq.x_is_nonpositive = Eq[-1].this.rhs.apply(Algebra.Le_0.Gt_0.to.Le_0)

    Eq << Sets.In.to.Gt_.Sqrt.Zero.apply(Eq[1])

    Eq << Algebra.Cond.to.Imply.And.apply(Eq[-1], cond=y > 0)

    Eq << Eq[-1].this.rhs.apply(Algebra.Gt_0.Gt_0.to.Gt_0)

    Eq << Algebra.Imply.Imply.to.Imply.And.apply(Eq.x_is_nonpositive, Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Le.Gt.to.Gt.trans)

    Eq << Eq.gt_le.this.lhs.apply(Algebra.Gt.Le.to.Gt.trans)

    Eq << Eq[-1].this.lhs.apply(Algebra.Gt.to.Ge.relax)

    Eq << Algebra.Cond.of.Cond.subs.Bool.apply(Eq[-1], cond=Eq[0], invert=True)

    Eq <<= Algebra.Cond.to.Imply.And.apply(Eq[1], cond=x > 0), Algebra.Cond.to.Imply.And.apply(Eq[2], cond=y > 0)

    Eq <<= Eq[-2].this.rhs.apply(Sets.Gt.In_Interval.to.In.Interval.Intersect), Eq[-1].this.rhs.apply(Sets.Gt.In_Interval.to.In.Interval.Intersect)

    Eq << Algebra.Imply.Imply.to.Imply.And.apply(Eq[-1], Eq[-2])

    Eq << Algebra.Cond.to.Imply.apply(Eq[0], cond=Eq[-1].lhs)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(Sets.Lt.In.In.to.Gt.Sqrt.open.positive)

    Eq <<= Algebra.Cond.to.Imply.And.apply(Eq[1], cond=x <= 0), Algebra.Cond.to.Imply.And.apply(Eq[2], cond=y <= 0)

    Eq <<= Eq[-2].this.rhs.apply(Sets.Le.In_Interval.to.In.Interval.Intersect), Eq[-1].this.rhs.apply(Sets.Le.In_Interval.to.In.Interval.Intersect)

    Eq << Algebra.Imply.Imply.to.Imply.And.apply(Eq[-1], Eq[-2])

    Eq << Algebra.Cond.to.Imply.apply(Eq[0], cond=Eq[-1].lhs)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(Sets.Lt.In.In.to.Gt.Sqrt.open.nonpositive)


if __name__ == '__main__':
    run()

# created on 2020-11-29
from . import nonnegative
from . import positive
from . import nonpositive
