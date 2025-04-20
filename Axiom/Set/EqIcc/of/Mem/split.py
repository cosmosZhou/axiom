from util import *


@apply
def apply(given, right_open=True):
    x, interval = given.of(Element)
    a, b = interval.of(Interval)
    return Equal(interval, Interval(a, x, left_open=interval.left_open, right_open=right_open) | Interval(x, b, left_open=not right_open, right_open=interval.right_open))


@prove
def prove(Eq):
    from Axiom import Set, Algebra, Logic

    x, a, b, t = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b, left_open=True)), right_open=False)

    Eq << Set.Eq.given.And.Imp.apply(Eq[1], t)

    Eq <<= Eq[-2].this.rhs.apply(Set.Mem_Union.given.OrMemS), Eq[-1].this.lhs.apply(Set.Or.of.Mem_Union)

    Eq <<= Eq[-2].this.lhs.apply(Set.And.of.Mem_Icc), Eq[-1].this.rhs.apply(Set.Mem_Icc.given.And)

    Eq <<= Eq[-2].this.find(Element).apply(Set.Mem_Icc.given.And), Eq[-1].this.find(Element).apply(Set.And.of.Mem_Icc)

    Eq <<= Eq[-2].this.find(Element).apply(Set.Mem_Icc.given.And), Eq[-1].this.find(Element).apply(Set.And.of.Mem_Icc)

    Eq << Logic.ImpOr.given.Imp.Imp.apply(Eq[-1])

    Eq <<= Logic.Imp.given.Imp.split.And.apply(Eq[-2], 1), Logic.Imp.given.Imp.split.And.apply(Eq[-1], 0)

    Eq << Set.And.of.Mem_Icc.apply(Eq[0])

    Eq <<= Logic.Imp.of.Cond.apply(Eq[-2], cond=t > x), Logic.Imp.of.Cond.apply(Eq[-1], cond=t <= x)

    Eq <<= Logic.Imp_And.of.ImpAnd.apply(Eq[-2]), Logic.Imp_And.of.ImpAnd.apply(Eq[-1])

    Eq <<= Eq[-2].this.rhs.apply(Algebra.Gt.of.Gt.Gt), Eq[-1].this.rhs.apply(Algebra.Le.of.Le.Le)


if __name__ == '__main__':
    run()
# created on 2020-11-22
