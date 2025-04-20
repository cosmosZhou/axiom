from util import *


@apply
def apply(a_is_negative, b_is_negative, lt, k=None):
    a = a_is_negative.of(Expr < 0)
    b = b_is_negative.of(Expr < 0)
    S[a], S[b] = lt.of(Less)
    assert a.is_integer and b.is_integer
    if k is None:
        k = a.generate_var(b.free_symbols, integer=True)
    return Equal(Cup[k:a:b](Interval(k, k + 1, left_open=True)), Interval(a, b, left_open=True))


@prove
def prove(Eq):
    from Axiom import Set, Algebra, Logic

    a, b = Symbol(integer=True, given=True)
    k = Symbol(integer=True)
    Eq << apply(a < 0, b < 0, a < b, k)

    Eq << Set.Cup.eq.Union.split.apply(Cup[k:a:0](Eq[-1].lhs.expr), cond=Range(b, 0))

    Eq.min_b0 = Algebra.EqMin.of.Lt.apply(Eq[1])

    Eq << Algebra.EqMax.of.Lt.apply(Eq[2])

    Eq <<= Eq[-2].rhs.args[0].this.subs(Eq.min_b0), Eq[-2].rhs.args[1].this.subs(Eq[-1])

    Eq << Set.Cup.eq.Icc.of.Lt_0.left_open.apply(Eq[1], k)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[4].subs(Eq[-1], Eq[-4]).reversed

    Eq << Set.Cup.eq.Icc.of.Lt_0.left_open.apply(Eq[0], k)

    Eq << Eq[-2].subs(Eq[-1])

    interval_b = Eq[-1].lhs.args[0]
    Eq << Set.EqSDiff.of.Eq.apply(Eq[-1], interval_b)

    Eq << Algebra.EqMax.of.Lt.apply(Eq[0])

    Eq.eq_complement = Eq[-2].subs(Eq[-1], Eq.min_b0)

    Eq.is_empty = Equal(Intersection(*Eq.eq_complement.lhs.args), Eq.eq_complement.rhs.etype.emptySet, plausible=True)

    Eq << ~Eq.is_empty

    Eq << Set.Any_Mem.of.Inter_Ne_EmptySet.apply(Eq[-1], simplify=None, index=1)

    Eq << Eq[-1].this.expr.apply(Set.Any_Mem.of.Mem_Cup)

    Eq << Algebra.Any.And.of.Any.limits.unleash.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Element).apply(Set.And.of.Mem_Range)

    Eq << Eq[-1].this.expr.apply(Logic.Cond.of.And, slice(0, 2))

    Eq << Algebra.Any.And.of.Cond.Any.apply(Eq[1], Eq[-1])

    Eq << Eq[-1].this.expr.args[1:].apply(Algebra.Lt.of.Lt.Lt, ret=1)

    Eq << Eq[-1].this.expr.args[1].apply(Algebra.Le.of.Lt.strengthen.plus)

    Eq << Eq[-1].this.expr.find(LessEqual).apply(Algebra.EqMin.of.Le)

    Eq << Eq[-1].this.expr.args[:2].apply(Logic.Cond.of.Eq.Cond.subs)

    Eq << Eq[-1].this.expr.args[1].apply(Algebra.EqMax.of.Lt, ret=0)

    Eq << Eq[-1].this.expr.args[:2].apply(Logic.Cond.of.Eq.Cond.subs)

    Eq << Eq[-1].this.expr.args[0].apply(Set.Gt.of.Icc_Ne_EmptySet)

    Eq << Eq[-1].this.find(Greater).apply(Algebra.Ge.of.Gt.strengthen)

    Eq << Set.EqUnionS.of.Eq.Eq.apply(Eq.eq_complement, Eq.is_empty)





if __name__ == '__main__':
    run()
# created on 2018-10-15
# updated on 2023-05-20
