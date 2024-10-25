from util import *


def is_differentiable_at(cond, dir=1):
    (dfx, domain), (x, a, b) = cond.of(All[Element])
    fx, (S[x + dir * S.Infinitesimal], S[1]) = dfx.of(Derivative)
    assert domain in Interval(-oo, oo, left_open=False, right_open=False)
    return fx, (x, a, b)

@apply
def apply(lt, is_continuous, left_is_real, right_is_real, equal):
    a, b = lt.of(Less)
    from axiom.calculus.lt.is_continuous.is_differentiable.eq.then.any.eq.Rolle import of_continuous
    fx, (x, S[a], S[b]) = of_continuous(is_continuous)
    S[fx], S[(x, a, b)] = is_differentiable_at(left_is_real)
    S[fx], S[(x, a, b)] = is_differentiable_at(right_is_real, -1)

    S[fx._subs(x, a)], S[fx._subs(x, b)] = equal.of(Equal)

    return Any[x:a:b](Derivative[x - S.Infinitesimal](fx) * Derivative[x + S.Infinitesimal](fx) <= 0)


@prove
def prove(Eq):
    from axiom import calculus, sets, algebra

    a, b, x = Symbol(real=True)
    f = Function(shape=(), real=True)
    from axiom.calculus.all_eq.then.all.any.eq.intermediate_value_theorem import is_continuous
    Eq << apply(
        a < b,
        is_continuous(f, a, b),
        All[x:a:b](Element(Derivative[x + S.Infinitesimal](f(x)), ExtendedReals)),
        All[x:a:b](Element(Derivative[x - S.Infinitesimal](f(x)), ExtendedReals)),
        Equal(f(a), f(b)))

    Eq << Eq[2].this.find(Derivative).apply(calculus.grad.to.limit.one_sided)

    Eq << Eq[3].this.find(Derivative).apply(calculus.grad.to.limit.one_sided)

    Eq << sets.lt.then.subset.finiteset.apply(Eq[0], simplify=None)

    Eq.eq_intersect = sets.subset.then.eq.intersect.apply(Eq[-1])

    ξ = Eq[1].variable
    c0, c1 = Symbol(real=True)
    Eq << calculus.lt.is_continuous.then.any.all.ge.extreme_value_theorem.apply(*Eq[:2]).limits_subs(ξ, c0)

    # Eq << Eq[-1].this.expr.expr.reversed
    Eq << algebra.any.then.ou.any.split.apply(Eq[-1], cond={a, b})

    Eq << Eq[-1].subs(Eq.eq_intersect)

    Eq << calculus.lt.is_continuous.then.any.all.le.extreme_value_theorem.apply(*Eq[:2]).limits_subs(ξ, c1)

    Eq << algebra.any.then.ou.any.split.apply(Eq[-1], cond={a, b})

    Eq << Eq[-1].subs(Eq.eq_intersect)

    Eq <<= Eq[-1] & Eq[-4]

    Eq << Eq[-1].this.apply(algebra.et.then.ou, simplify=None)

    Eq << Eq[-1].this.find(And[Or]).apply(algebra.et.then.ou, simplify=None)

    Eq << Eq[-1].this.find(And).apply(algebra.any.any.then.any.et)

    Eq << Eq[-1].this.find(And).apply(algebra.et.then.cond, 1)

    Eq << Eq[-1].this.find(And).apply(algebra.et.then.cond)

    Eq << algebra.cond.of.et.infer.apply(Eq[5], cond=Eq[-1])

    Eq.any_max, Eq.any_min, Eq.any_boundary = algebra.infer_ou.of.et.infer.apply(Eq[-1], None)

    Eq <<= Eq.any_min.this.lhs.apply(algebra.any.then.any.et.limits.unleash, simplify=None), \
        Eq.any_max.this.lhs.apply(algebra.any.then.any.et.limits.unleash, simplify=None)

    Eq <<= Eq[1] & Eq[2] & Eq[3]

    Eq <<= algebra.infer.of.et.infer.invert.apply(Eq[-3], cond=Eq[-1]), algebra.infer.of.et.infer.invert.apply(Eq[-2], cond=Eq[-1])

    Eq <<= algebra.ou.of.cond.apply(Eq[-3], 0), algebra.ou.of.cond.apply(Eq[-1], 0)

    Eq <<= Eq[-4].this.lhs.args[:2].apply(algebra.cond.any.then.any.et, simplify=None), \
        Eq[-2].this.lhs.args[:2].apply(algebra.cond.any.then.any.et, simplify=None)

    Eq <<= Eq[-2].this.lhs.args[:2].apply(algebra.cond.any.then.any.et, simplify=None), \
        Eq[-1].this.lhs.args[:2].apply(algebra.cond.any.then.any.et, simplify=None)

    Eq.any_et_min = Eq[-2].this.lhs.apply(algebra.cond.any.then.any.et, simplify=None)

    Eq.any_et_max = Eq[-1].this.lhs.apply(algebra.cond.any.then.any.et, simplify=None)

    et = And(*Eq.any_et_max.lhs.expr.args)
    Eq <<= et.this.apply(algebra.et.then.cond, slice(0, 4)), et.this.apply(algebra.et.then.cond, slice(3, 2, -1))

    Eq <<= Eq[-2].this.rhs.find(All[LessEqual]).apply(algebra.all.then.all.limits.restrict, Interval.open(a, b), simplify=None), Eq[-1].this.rhs.find(All[LessEqual]).apply(algebra.all.then.all.limits.restrict, Interval.open(a, b), simplify=None)

    Eq <<= Eq[-2].this.rhs.apply(calculus.el_interval.is_continuous.is_extended_real.all_le.then.le_zero.subs.grad), Eq[-1].this.rhs.apply(calculus.el_interval.is_continuous.is_extended_real.all_le.then.ge_zero.subs.grad)

    Eq <<= Eq[-2] & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(algebra.le_zero.ge_zero.then.le_zero)

    Eq << algebra.infer_et.then.infer.et.apply(Eq[-1], 0)

    Eq << algebra.infer.then.infer.any.apply(Eq[-1], c1)

    Eq << Eq[-1].this.rhs.apply(algebra.any_et.then.any.limits_absorb, 1)

    Eq << Eq[-1].this.rhs.limits_subs(c1, x)

    et = And(*Eq.any_et_min.lhs.expr.args)
    Eq <<= et.this.apply(algebra.et.then.cond, slice(0, 4)), et.this.apply(algebra.et.then.cond, slice(3, 2, -1))

    Eq <<= Eq[-2].this.rhs.find(All[GreaterEqual]).apply(algebra.all.then.all.limits.restrict, Interval.open(a, b), simplify=None), Eq[-1].this.rhs.find(All[GreaterEqual]).apply(algebra.all.then.all.limits.restrict, Interval.open(a, b), simplify=None)

    Eq <<= Eq[-2].this.rhs.apply(calculus.el_interval.is_continuous.is_extended_real.all_ge.then.ge_zero.subs.grad), Eq[-1].this.rhs.apply(calculus.el_interval.is_continuous.is_extended_real.all_ge.then.le_zero.subs.grad)

    Eq <<= Eq[-2] & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(algebra.le_zero.ge_zero.then.le_zero)

    Eq << algebra.infer_et.then.infer.et.apply(Eq[-1], 0)

    Eq << algebra.infer.then.infer.any.apply(Eq[-1], c0)

    Eq << Eq[-1].this.rhs.apply(algebra.any_et.then.any.limits_absorb, 1)

    Eq << Eq[-1].this.rhs.limits_subs(c0, x)

    Eq << Eq.any_boundary.this.lhs.apply(algebra.any.then.any.et.limits.unleash, simplify=None)

    Eq << algebra.cond.infer.of.et.infer.et.apply(Eq[4], Eq[-1])

    Eq << Eq[-1].this.lhs.apply(algebra.cond.any.then.any.et, simplify=None)

    Eq << Eq[-1].this.find(And).args[:-1].apply(sets.el_finiteset.el_finiteset.eq.then.eq)

    Eq << Eq[-1].this.find(And).apply(algebra.eq.cond.then.cond.subs)

    Eq << Eq[-1].this.find(And).apply(algebra.le.ge.then.eq)

    Eq << Eq[-1].this.find(Equal).apply(calculus.eq.then.eq.grad, (x,))

    Eq << Eq[-1].this.find(Equal).rhs.doit()

    Eq << Eq[-1].this.find(Equal).apply(calculus.eq_grad.then.et.eq_grad)

    Eq << Eq[-1].this.find(And).apply(algebra.eq.eq.then.eq.mul)

    Eq << Eq[-1].this.find(Equal).apply(algebra.eq.then.le)

    Eq << Eq[-1].this.lhs.apply(algebra.all.then.all.limits.restrict, Interval.open(a, b))

    Eq << Eq[-1].this.rhs.apply(algebra.any.of.cond.subs, x, (a + b) / 2)

    Eq << Eq[-1].this.lhs.apply(algebra.all.then.cond.subs, x, (a + b) / 2)

    Eq << algebra.infer.of.cond.apply(Eq[-1])

    Eq << sets.lt.then.el.interval.average.apply(Eq[0])





if __name__ == '__main__':
    run()
# created on 2023-10-14
# updated on 2023-11-10
