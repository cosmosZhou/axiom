from util import *


@apply
def apply(el_interval, is_continuous, is_extended_real, all_le):
    from axiom.calculus.lt.is_continuous.is_differentiable.eq.then.any.eq.Rolle import of_continuous
    fx, limit = of_continuous(is_continuous)
    x, a, b = limit

    from axiom.calculus.lt.is_continuous.is_extended_real.is_extended_real.eq.then.any.le.Rolle import is_differentiable_at
    S[fx], S[limit] = is_differentiable_at(is_extended_real, -1)

    c, S[Interval.open(a, b)] = el_interval.of(Element)
    (S[fx], S[fx._subs(x, c)]), S[limit] = all_le.of(All[LessEqual])
    return Subs[x:c](Derivative[x - S.Infinitesimal](fx)) >= 0


@prove
def prove(Eq):
    from axiom import calculus, algebra, sets

    a, b, x, c = Symbol(real=True)
    f = Function(shape=(), real=True)
    from axiom.calculus.all_eq.then.all.any.eq.intermediate_value_theorem import is_continuous
    Eq << apply(
        Element(c, Interval.open(a, b)),
        is_continuous(f, a, b),
        All[x:a:b](Element(Derivative[x - S.Infinitesimal](f(x)), ExtendedReals)),
        All[x:a:b](f(x) <= f(c)))

    Eq <<= Eq[-1].this.find(Derivative).apply(calculus.grad.to.limit.one_sided), algebra.all.then.all.limits.subs.offset.apply(Eq[-2], c)

    Eq << algebra.all.then.infer.apply(Eq[-1])

    Eq << sets.el.then.el.sub.apply(Eq[0], c)

    Eq.lt_zero = sets.el_interval.then.gt.apply(Eq[-1]).this.apply(algebra.gt.then.lt_zero)

    Eq << algebra.cond.infer.then.infer.et.lhs.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.lhs.apply(sets.el.el.of.et.el, stop=True)

    Eq << algebra.cond.cond.then.cond.subs.apply(Eq[-3], Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.le.then.le_zero)

    Eq << algebra.infer.then.infer.et.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(sets.is_negative.le.then.ge.div)

    Eq << algebra.infer.then.all.apply(Eq[-1])

    Eq << sets.lt_zero.then.is_negative.apply(Eq.lt_zero, simplify=None)

    δ = Symbol(real=True, negative=True)
    Eq << sets.el.then.any.eq.apply(Eq[-1], var=δ)

    Eq << algebra.cond.any.then.any.et.apply(Eq[-3], Eq[-1], simplify=None)

    Eq.any_all = Eq[-1].this.expr.apply(algebra.eq.cond.then.cond.subs)

    Eq << algebra.all.then.infer.apply(Eq[2])

    Eq << Eq[-1].subs(x, c)

    Eq << algebra.cond.infer.then.cond.trans.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].this.find(Derivative).apply(calculus.grad.to.limit.one_sided, simplify=2)

    Eq << Eq.any_all.this.find(All).limits_subs(x, Eq[-1].lhs.variable)

    Eq << algebra.cond.any.then.any.et.apply(Eq[-1], Eq.any_all, simplify=None)


    Eq << Eq[-1].this.expr.apply(calculus.is_extended_real.all_ge.then.ge_zero.limit.one_sided)



if __name__ == '__main__':
    run()
# created on 2023-10-15
