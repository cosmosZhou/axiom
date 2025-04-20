from util import *


@apply
def apply(lt_a, lt_b, right_open=True, left_open=None):
    a, x = lt_a.of(Less)
    S[x], b = lt_b.of(LessEqual)
    if left_open is not None:
        right_open = not left_open
    return Equal(Interval(a, x, left_open=True, right_open=right_open) | Interval(x, b, left_open=not right_open, right_open=True), Interval(a, b, left_open=True, right_open=True))


@prove
def prove(Eq):
    from Axiom import Set, Algebra, Logic

    a, b, x = Symbol(real=True, given=True)
    Eq << apply(a < x, x <= b)

    Eq << Set.Eq.given.And.Imp.apply(Eq[2])

    Eq <<= Eq[-2].this.lhs.apply(Set.Or.of.Mem_Union), Eq[-1].this.rhs.apply(Set.Mem_Union.given.OrMemS)

    Eq <<= Logic.ImpOr.given.Imp.Imp.apply(Eq[-2]), Eq[-1].this.apply(Logic.Imp.contraposition)

    Eq <<= Eq[-3].this.lhs.apply(Set.And.of.Mem_Icc), Eq[-2].this.lhs.apply(Set.And.of.Mem_Icc), Eq[-1].this.lhs.args[0].apply(Set.Or.of.NotMem_Icc)

    Eq <<= Eq[-3].this.rhs.apply(Set.Mem_Icc.given.And), Eq[-2].this.rhs.apply(Set.Mem_Icc.given.And), Eq[-1].this.lhs.find(NotElement).apply(Set.Or.of.NotMem_Icc)

    Eq <<= Logic.Imp.And.of.Cond.apply(Eq[1], cond=Eq[-3].lhs), Logic.Imp.And.of.Cond.apply(Eq[0], cond=Eq[-2].lhs), Eq[-1].this.rhs.apply(Set.NotMem_Icc.given.Or)

    Eq <<= Eq[-3].this.rhs.args[::2].apply(Algebra.Lt.of.Le.Lt), Eq[-2].this.rhs.args[::2].apply(Algebra.Gt.of.Lt.Ge),  Eq[-1].this.lhs.apply(Logic.OrAndS.of.And_Or)

    Eq << Logic.ImpOr.given.Imp.Imp.apply(Eq[-1])

    Eq << Logic.Imp.given.Imp.split.And.apply(Eq[-2], 1)

    Eq << Logic.Imp.given.Imp.split.And.apply(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2021-06-02
# updated on 2023-05-20
