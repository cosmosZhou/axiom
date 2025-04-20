from util import *


@apply
def apply(self):
    interval, k = self.of(Cup[Tuple[0, oo]])
    S[k], S[k + 1] = interval.of(Interval)
    assert not interval.left_open and interval.right_open

    return Equal(self, Interval(0, oo, right_open=True))


@prove
def prove(Eq):
    from Axiom import Set, Algebra, Logic

    k = Symbol(integer=True)
    Eq << apply(Cup[k:oo](Interval(k, k + 1, right_open=True)))

    Eq << Set.Eq.given.And.Imp.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(Set.Any_Mem.of.Mem_Cup), Eq[-1].this.rhs.apply(Set.Mem_Cup.given.Any_Mem)

    k = Eq[-1].rhs.variable
    x = Eq[-1].lhs.lhs
    Eq <<= Eq[-2].this.lhs.expr.apply(Set.Ge.of.Mem_Icc), Eq[-1].this.rhs.apply(Algebra.Any.given.Cond.subs, k, Floor(x))

    Eq <<= Eq[-2].this.lhs.apply(Algebra.Any.And.of.Any.limits.unleash, simplify=None), Logic.Imp_And.given.Imp.Imp.apply(Eq[-1])

    Eq <<= Eq[-3].this.lhs.find(Element).apply(Set.Ge.of.Mem_Range), Logic.Imp.given.Cond.apply(Eq[-2]), Eq[-1].this.rhs.apply(Set.Mem_Range.given.And)

    Eq << Eq[-1].this.lhs.apply(Set.Ge.of.Mem_Icc)

    Eq <<= Eq[-3].this.lhs.expr.apply(Algebra.Ge.of.Ge.Ge), Set.Mem_Icc.given.And.apply(Eq[-2])

    Eq << Eq[-3].this.lhs.apply(Set.IsNotNegative.of.Ge_0, simplify=None)

    Eq << Algebra.Lt_Add_.Floor.One.apply(x)

    Eq << Algebra.Ge_Floor.apply(x)




if __name__ == '__main__':
    run()
# created on 2021-02-14
# updated on 2023-05-14
