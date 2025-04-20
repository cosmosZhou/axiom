from util import *


@apply
def apply(lt, x=None, left_open=True, right_open=True):
    m, M = lt.of(Less)
    return Equal(Sup[x:Interval(m, M, left_open=left_open, right_open=right_open)](x), M)


@prove
def prove(Eq):
    from Axiom import Algebra, Set, Logic

    m, M, a, b = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(m < M, x)

    Eq.eq_min = Algebra.EqMin.of.Lt.apply(Eq[0])

    Eq << Algebra.Eq.given.And.squeeze.apply(Eq[-1])

    y = Symbol(real=True)
    Eq <<= Algebra.GeSup.given.All_Any_Gt.apply(Eq[-1], y), Algebra.LeSup.given.All.Le.apply(Eq[-2])

    Eq <<= Algebra.All.given.And.All.split.apply(Eq[-2], cond=y < m), Algebra.All.given.Or.apply(Eq[-1])

    Eq <<= Eq[-2].subs(Eq.eq_min), Eq[-3].this.expr.apply(Algebra.Any.given.Cond.subs, x, (M + y) / 2), Eq[-1].this.find(NotElement).apply(Set.NotMem_Icc.given.Or)

    Eq <<= Eq[-2].this.expr.apply(Algebra.Any.given.Cond.subs, x, (m + M) / 2), Algebra.All_And.given.And.All.apply(Eq[-1])

    Eq <<= Algebra.And.given.And.apply(Eq[-3]), Logic.All.given.Imp.apply(Eq[-2]), Logic.All.given.Imp.apply(Eq[-1])

    Eq << Set.Mem.Icc.of.Lt.average.apply(Eq[0])

    Eq <<= Logic.All.given.Imp.apply(Eq[-3]), Eq[-2].this.rhs * 2, Eq[-1].this.rhs.apply(Set.Mem.given.Mem.Mul.Icc, 2)

    Eq <<= Logic.Cond.Imp.given.And.Imp.And.apply(Eq[0], Eq[-3]), Eq[-2].this.rhs - y, Eq[-1].this.rhs.apply(Set.Mem.given.Mem.Sub, M)

    Eq << Eq[-2].this.lhs.apply(Set.Gt.of.Mem_Icc)

    Eq <<= Eq[-3].this.lhs.apply(Algebra.Lt.of.Lt.Lt, ret=1), Eq[-1].this.rhs.apply(Set.Mem.given.And.strengthen, upper=m, strict=True)

    Eq <<= Eq[-2].this.lhs.apply(Algebra.LtAdd.of.Lt.Lt), Logic.Imp.given.Cond.apply(Eq[-1])

    Eq << Eq[-1] + (M - m)

    Eq << Eq[-2].this.rhs * 2




if __name__ == '__main__':
    run()
# created on 2019-09-10
# updated on 2023-05-20

