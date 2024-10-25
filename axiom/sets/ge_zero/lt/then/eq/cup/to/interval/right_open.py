from util import *


@apply
def apply(is_nonnegative, lt, k=None):
    a = is_nonnegative.of(Expr >= 0)
    S[a], b = lt.of(Less)
    assert a.is_integer and b.is_integer
    if k is None:
        k = lt.generate_var(integer=True)
    return Equal(Cup[k:a:b](Interval(k, k + 1, right_open=True)), Interval(a, b, right_open=True))


@prove
def prove(Eq):
    from axiom import algebra, sets

    a, b = Symbol(integer=True, given=True)
    k = Symbol(integer=True)
    Eq << apply(a >= 0, a < b, k)

    Eq << algebra.lt.then.eq.min.apply(Eq[1])

    Eq << algebra.eq.ge.then.ge.add.apply(Eq[-1], Eq[0])

    Eq << sets.ge_zero.then.eq.cup.to.interval.right_open.apply(Eq[-1], k)

    Eq << Eq[-1].this.rhs.subs(Eq[-3])

    Eq << sets.cup.to.union.split.apply(Cup[k:b](Eq[-1].lhs.expr), cond=Range(a))

    Eq << Eq[-1].subs(Eq[-2])

    Eq.b_is_nonnegative = algebra.ge.lt.then.ge.relax.apply(Eq[0], Eq[1])

    Eq << sets.ge_zero.then.eq.cup.to.interval.right_open.apply(Eq.b_is_nonnegative, k)

    Eq << Eq[-2].subs(Eq[-1])

    interval_a = Eq[-1].rhs.args[0]
    Eq << sets.eq.then.eq.complement.apply(Eq[-1], interval_a)

    Eq << algebra.ge.then.eq.max.apply(Eq[0])

    Eq.eq_complement = Eq[-2].subs(Eq[-1]).reversed

    Eq.is_empty = Equal(Intersection(*Eq.eq_complement.lhs.args), Eq.eq_complement.rhs.etype.emptySet, plausible=True)

    Eq << ~Eq.is_empty

    Eq << sets.intersect_ne_empty.then.any_el.apply(Eq[-1], simplify=None, index=1)

    Eq << Eq[-1].this.expr.apply(sets.el_cup.then.any_el)

    Eq << algebra.any.then.any.et.limits.unleash.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Element).apply(sets.el_range.then.et)

    Eq << Eq[-1].this.expr.apply(algebra.et.then.cond, slice(0, 3, 2))

    Eq << Eq[-1].this.find(GreaterEqual).apply(algebra.ge.then.gt.relax, step=1, ret=0)

    Eq << Eq[-1].this.find(Greater).apply(algebra.gt.then.eq.min)

    Eq << Eq[-1].this.expr.args[:2].apply(algebra.eq.cond.then.cond.subs)

    Eq << algebra.cond.any.then.any.et.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].this.expr.args[1:].apply(algebra.ge.ge.then.ge.trans, ret=1)

    Eq << Eq[-1].this.expr.args[1].apply(algebra.ge.then.eq.max)

    Eq << Eq[-1].this.expr.args[:2].apply(algebra.eq.cond.then.cond.subs)

    Eq << Eq[-1].this.expr.args[0].apply(sets.interval_ne_empty.then.gt)

    Eq << sets.intersect_is_empty.eq_complement.then.eq.apply(Eq.is_empty, Eq.eq_complement)





if __name__ == '__main__':
    run()
# created on 2021-02-20
# updated on 2023-11-05
