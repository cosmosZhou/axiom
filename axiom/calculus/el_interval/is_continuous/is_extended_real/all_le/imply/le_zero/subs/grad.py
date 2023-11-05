from util import *


@apply
def apply(el_interval, is_continuous, is_extended_real, all_le):
    from axiom.calculus.lt.is_continuous.is_differentiable.eq.imply.any_eq.Rolle import of_continuous
    fx, limit = of_continuous(is_continuous)
    x, a, b = limit

    from axiom.calculus.lt.is_continuous.is_extended_real.is_extended_real.eq.imply.any_le.Rolle import is_differentiable_at
    S[fx], S[limit] = is_differentiable_at(is_extended_real)

    c, S[Interval.open(a, b)] = el_interval.of(Element)
    (S[fx], S[fx._subs(x, c)]), S[limit] = all_le.of(All[LessEqual])
    return Subs[x:c](Derivative[x + S.Infinitesimal](fx)) <= 0


@prove
def prove(Eq):
    from axiom import calculus, algebra, sets

    a, b, x, c = Symbol(real=True)
    f = Function(shape=(), real=True)
    from axiom.calculus.all_eq.imply.all.any.eq.intermediate_value_theorem import is_continuous
    Eq << apply(
        Element(c, Interval.open(a, b)),
        is_continuous(f, a, b),
        All[x:a:b](Element(Derivative[x + S.Infinitesimal](f(x)), ExtendedReals)),
        All[x:a:b](f(x) <= f(c)))

    Eq <<= Eq[-1].this.find(Derivative).apply(calculus.grad.to.limit.one_sided), algebra.all.imply.all.limits.subs.offset.apply(Eq[-2], c)

    Eq << algebra.all.imply.infer.apply(Eq[-1])

    Eq << sets.el.imply.el.sub.apply(Eq[0], c)

    Eq.gt_zero = sets.el_interval.imply.lt.apply(Eq[-1]).this.apply(algebra.lt.imply.gt_zero)

    Eq << algebra.cond.infer.imply.infer.et.lhs.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.lhs.apply(sets.el.el.given.et.el)

    Eq << algebra.cond.cond.imply.cond.subs.apply(Eq[-3], Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.le.imply.le_zero)

    Eq << algebra.infer.imply.infer.et.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(sets.is_positive.le.imply.le.div)

    Eq << algebra.infer.imply.all.apply(Eq[-1])

    Eq << sets.gt_zero.imply.is_positive.apply(Eq.gt_zero, simplify=None)

    δ = Symbol(real=True, positive=True)
    Eq << sets.el.imply.any_eq.apply(Eq[-1], var=δ)

    Eq << algebra.cond.any.imply.any.et.apply(Eq[-3], Eq[-1], simplify=None)

    Eq.any_all = Eq[-1].this.expr.apply(algebra.eq.cond.imply.cond.subs)

    Eq << algebra.all.imply.infer.apply(Eq[2])

    Eq << Eq[-1].subs(x, c)

    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].this.find(Derivative).apply(calculus.grad.to.limit.one_sided, simplify=2)

    Eq << Eq.any_all.this.find(All).limits_subs(x, Eq[-1].lhs.variable)

    Eq << algebra.cond.any.imply.any.et.apply(Eq[-1], Eq.any_all, simplify=None)

    Eq << Eq[-1].this.expr.apply(calculus.is_extended_real.all_le.imply.le_zero.limit.one_sided)

    


if __name__ == '__main__':
    run()
# created on 2023-10-15
