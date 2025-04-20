from util import *


@apply
def apply(self):
    interval, k = self.of(Cup[Tuple[0, oo]])
    S[k], S[k + 1] = interval.of(Interval)
    assert interval.left_open and not interval.right_open

    return Equal(self, Interval.open(0, oo))


@prove
def prove(Eq):
    from Axiom import Set, Algebra, Logic

    k = Symbol(integer=True)
    Eq << apply(Cup[k:oo](Interval(k, k + 1, left_open=True)))

    Eq << Set.Eq.given.And.Imp.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(Set.Any_Mem.of.Mem_Cup), Eq[-1].this.rhs.apply(Set.Mem_Cup.given.Any_Mem)

    k = Eq[-1].rhs.variable
    x = Eq[-1].lhs.lhs
    Eq <<= Eq[-2].this.lhs.expr.apply(Set.Gt.of.Mem_Icc), Eq[-1].this.rhs.apply(Algebra.Any.given.Cond.subs, k, Ceil(x) - 1)

    Eq <<= Eq[-2].this.lhs.apply(Algebra.Any.And.of.Any.limits.unleash, simplify=None), Logic.Imp_And.given.Imp.Imp.apply(Eq[-1])

    Eq <<= Eq[-3].this.lhs.find(Element).apply(Set.Ge.of.Mem_Range), Logic.Imp.given.Cond.apply(Eq[-2]), Eq[-1].this.rhs.apply(Set.Mem_Range.given.And)

    Eq <<= Eq[-3].this.lhs.expr.apply(Algebra.Gt.of.Gt.Ge), Set.Mem_Icc.given.And.apply(Eq[-2]), Eq[-1].this.rhs.apply(Algebra.Ge.transport, lhs=0)

    Eq << Eq[-4].this.lhs.apply(Set.IsPositive.of.Gt_0, simplify=None)

    Eq << Algebra.Gt_Sub_.Ceil.One.apply(x)

    Eq << Algebra.Le_Ceil.apply(x)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Eq[-1].this.lhs.apply(Algebra.Gt_0.Ceil.of.Gt_0)

    Eq << Eq[-1].this.lhs.apply(Algebra.Ge.of.Gt.strengthen)




if __name__ == '__main__':
    run()
# created on 2021-02-13
# updated on 2023-05-12
