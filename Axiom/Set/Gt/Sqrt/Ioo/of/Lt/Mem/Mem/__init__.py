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
    from Axiom import Algebra, Set, Logic

    x, y = Symbol(real=True)
    Eq << apply(x < y, Element(x, Interval(-1, 1, left_open=True, right_open=True)), Element(y, Interval(-1, 1, left_open=True, right_open=True)))

    Eq << Logic.Cond.given.And.Imp.split.apply(Eq[-1], cond=y > 0)

    Eq <<= Logic.Cond.given.And.Imp.split.apply(Eq[-2], cond=x > 0), Logic.Cond.given.And.Imp.split.apply(Eq[-1], cond=x > 0)

    Eq.gt_gt, Eq.le_gt, Eq.gt_le, Eq.le_le = Eq[-4].this.apply(Logic.Imp.flatten), Eq[-3].this.apply(Logic.Imp.flatten), Eq[-2].this.apply(Logic.Imp.flatten), Eq[-1].this.apply(Logic.Imp.flatten)

    Eq << Set.Sqrt.gt.Zero.of.Mem.apply(Eq[2])

    Eq << Logic.Imp.And.of.Cond.apply(Eq[-1], cond=x <= 0)

    Eq.x_is_nonpositive = Eq[-1].this.rhs.apply(Algebra.Le_0.of.Le_0.Gt_0)

    Eq << Set.Sqrt.gt.Zero.of.Mem.apply(Eq[1])

    Eq << Logic.Imp.And.of.Cond.apply(Eq[-1], cond=y > 0)

    Eq << Eq[-1].this.rhs.apply(Algebra.Gt_0.of.Gt_0.Gt_0)

    Eq << Logic.ImpAndS.of.Imp.Imp.apply(Eq.x_is_nonpositive, Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Gt.of.Le.Gt)

    Eq << Eq.gt_le.this.lhs.apply(Algebra.Gt.of.Gt.Le)

    Eq << Eq[-1].this.lhs.apply(Algebra.Ge.of.Gt.relax)

    Eq << Algebra.Cond.given.Cond.subs.Bool.apply(Eq[-1], cond=Eq[0], invert=True)

    Eq <<= Logic.Imp.And.of.Cond.apply(Eq[1], cond=x > 0), Logic.Imp.And.of.Cond.apply(Eq[2], cond=y > 0)

    Eq <<= Eq[-2].this.rhs.apply(Set.Mem.Icc.Inter.of.Gt.Mem_Icc), Eq[-1].this.rhs.apply(Set.Mem.Icc.Inter.of.Gt.Mem_Icc)

    Eq << Logic.ImpAndS.of.Imp.Imp.apply(Eq[-1], Eq[-2])

    Eq << Logic.Imp.of.Cond.apply(Eq[0], cond=Eq[-1].lhs)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(Set.Gt.Sqrt.Ioo.of.Lt.Mem.Mem.positive)

    Eq <<= Logic.Imp.And.of.Cond.apply(Eq[1], cond=x <= 0), Logic.Imp.And.of.Cond.apply(Eq[2], cond=y <= 0)

    Eq <<= Eq[-2].this.rhs.apply(Set.Mem.Icc.Inter.of.Le.Mem_Icc), Eq[-1].this.rhs.apply(Set.Mem.Icc.Inter.of.Le.Mem_Icc)

    Eq << Logic.ImpAndS.of.Imp.Imp.apply(Eq[-1], Eq[-2])

    Eq << Logic.Imp.of.Cond.apply(Eq[0], cond=Eq[-1].lhs)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(Set.Gt.Sqrt.Ioo.of.Lt.Mem.Mem.nonpositive)


if __name__ == '__main__':
    run()

# created on 2020-11-29
from . import nonpositive
from . import positive
from . import nonnegative
