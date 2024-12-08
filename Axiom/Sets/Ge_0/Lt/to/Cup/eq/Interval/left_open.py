from util import *


@apply
def apply(is_nonnegative, lt, k=None):
    a = is_nonnegative.of(Expr >= 0)
    S[a], b = lt.of(Less)

    assert a.is_integer and b.is_integer
    if k is None:
        k = lt.generate_var(integer=True)
    return Equal(Cup[k:a:b](Interval(k, k + 1, left_open=True)), Interval(a, b, left_open=True))


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    a, b = Symbol(integer=True, given=True)
    k = Symbol(integer=True)
    Eq << apply(a >= 0, a < b, k)

    Eq << Algebra.Lt.to.Eq.Min.apply(Eq[1])

    Eq << Algebra.Eq.Ge.to.Ge.Add.apply(Eq[-1], Eq[0])

    Eq << Sets.Ge_0.to.Cup.eq.Interval.left_open.apply(Eq[-1], k)

    Eq << Eq[-1].this.rhs.subs(Eq[-3])

    Eq << Sets.Cup.eq.Union.split.apply(Cup[k:b](Eq[-1].lhs.expr), cond=Range(a))

    Eq << Eq[-1].subs(Eq[-2])

    Eq.b_is_nonnegative = Algebra.Ge.Lt.to.Ge.relax.apply(Eq[0], Eq[1])

    Eq << Sets.Ge_0.to.Cup.eq.Interval.left_open.apply(Eq.b_is_nonnegative, k)

    Eq << Eq[-2].subs(Eq[-1])

    interval_a = Eq[-1].rhs.args[0]
    Eq << Sets.Eq.to.Eq.Complement.apply(Eq[-1], interval_a)

    Eq << Algebra.Ge.to.Eq.Min.apply(Eq.b_is_nonnegative)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Algebra.Ge.to.Eq.Max.apply(Eq[0])

    Eq.eq_complement = Eq[-2].subs(Eq[-1]).reversed

    Eq.is_empty = Equal(Intersection(*Eq.eq_complement.lhs.args), Eq.eq_complement.rhs.etype.emptySet, plausible=True)

    Eq << ~Eq.is_empty

    Eq << Sets.Intersect_Ne_EmptySet.to.Any_In.apply(Eq[-1], simplify=None, index=1)

    Eq << Eq[-1].this.expr.apply(Sets.In_Cup.to.Any_In)

    Eq << Algebra.Any.to.Any.And.limits.unleash.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Element).apply(Sets.In_Range.to.And)

    Eq << Eq[-1].this.expr.apply(Algebra.And.to.Cond, slice(0, 3, 2))

    Eq << Eq[-1].this.find(GreaterEqual).apply(Algebra.Ge.to.Gt.relax, step=1, ret=0)

    Eq << Eq[-1].this.find(Greater).apply(Algebra.Gt.to.Eq.Min)

    Eq << Eq[-1].this.expr.args[:2].apply(Algebra.Eq.Cond.to.Cond.subs)

    Eq << Algebra.Cond.Any.to.Any.And.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].this.expr.args[1:].apply(Algebra.Ge.Ge.to.Ge.trans, ret=1)

    Eq << Eq[-1].this.expr.args[1].apply(Algebra.Ge.to.Eq.Max)

    Eq << Eq[-1].this.expr.args[:2].apply(Algebra.Eq.Cond.to.Cond.subs)

    Eq << Eq[-1].this.expr.args[0].apply(Sets.Interval_Ne_EmptySet.to.Gt)

    Eq << Sets.Intersect_Eq_EmptySet.Eq_Complement.to.Eq.apply(Eq.is_empty, Eq.eq_complement)





if __name__ == '__main__':
    run()
# created on 2018-09-17
# updated on 2023-11-05
