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
    from Axiom import Sets, Algebra

    a, b = Symbol(integer=True, given=True)
    k = Symbol(integer=True)
    Eq << apply(a < 0, b < 0, a < b, k)

    Eq << Sets.Cup.eq.Union.split.apply(Cup[k:a:0](Eq[-1].lhs.expr), cond=Range(b, 0))

    Eq.min_b0 = Algebra.Lt.to.Eq.Min.apply(Eq[1])

    Eq << Algebra.Lt.to.Eq.Max.apply(Eq[2])

    Eq <<= Eq[-2].rhs.args[0].this.subs(Eq.min_b0), Eq[-2].rhs.args[1].this.subs(Eq[-1])

    Eq << Sets.Lt_0.to.Cup.eq.Interval.left_open.apply(Eq[1], k)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[4].subs(Eq[-1], Eq[-4]).reversed

    Eq << Sets.Lt_0.to.Cup.eq.Interval.left_open.apply(Eq[0], k)

    Eq << Eq[-2].subs(Eq[-1])

    interval_b = Eq[-1].lhs.args[0]
    Eq << Sets.Eq.to.Eq.Complement.apply(Eq[-1], interval_b)

    Eq << Algebra.Lt.to.Eq.Max.apply(Eq[0])

    Eq.eq_complement = Eq[-2].subs(Eq[-1], Eq.min_b0)

    Eq.is_empty = Equal(Intersection(*Eq.eq_complement.lhs.args), Eq.eq_complement.rhs.etype.emptySet, plausible=True)

    Eq << ~Eq.is_empty

    Eq << Sets.Intersect_Ne_EmptySet.to.Any_In.apply(Eq[-1], simplify=None, index=1)

    Eq << Eq[-1].this.expr.apply(Sets.In_Cup.to.Any_In)

    Eq << Algebra.Any.to.Any.And.limits.unleash.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Element).apply(Sets.In_Range.to.And)

    Eq << Eq[-1].this.expr.apply(Algebra.And.to.Cond, slice(0, 2))

    Eq << Algebra.Cond.Any.to.Any.And.apply(Eq[1], Eq[-1])

    Eq << Eq[-1].this.expr.args[1:].apply(Algebra.Lt.Lt.to.Lt.trans, ret=1)

    Eq << Eq[-1].this.expr.args[1].apply(Algebra.Lt.to.Le.strengthen.plus)

    Eq << Eq[-1].this.expr.find(LessEqual).apply(Algebra.Le.to.Eq.Min)

    Eq << Eq[-1].this.expr.args[:2].apply(Algebra.Eq.Cond.to.Cond.subs)

    Eq << Eq[-1].this.expr.args[1].apply(Algebra.Lt.to.Eq.Max, ret=0)

    Eq << Eq[-1].this.expr.args[:2].apply(Algebra.Eq.Cond.to.Cond.subs)

    Eq << Eq[-1].this.expr.args[0].apply(Sets.Interval_Ne_EmptySet.to.Gt)

    Eq << Eq[-1].this.find(Greater).apply(Algebra.Gt.to.Ge.strengthen)

    Eq << Sets.Eq.Eq.to.Eq.Union.apply(Eq.eq_complement, Eq.is_empty)





if __name__ == '__main__':
    run()
# created on 2018-10-15
# updated on 2023-05-20
