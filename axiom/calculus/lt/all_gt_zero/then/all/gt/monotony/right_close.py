from util import *


@apply
def apply(lt, given):
    a, b = lt.of(Less)
    (fx, (x, S[1])), (S[x], domain) = given.of(All[Derivative > 0])
    S[a], S[b] = domain.of(Interval)
    assert domain.is_closed

    return All[x:Interval(a, b, left_open=True)](Greater(fx, fx._subs(x, a)))


@prove(proved=False)
def prove(Eq):
    from axiom import sets, calculus, algebra

    a, b = Symbol(real=True, given=True)
    domain = Interval(a, b)
    x, t = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(a < b, All[x:domain](Derivative[x](f(x)) > 0))

    Eq << Eq[1].this.expr.apply(sets.gt_zero.then.is_real)

    Eq.is_continuous = calculus.is_differentiable.then.is_continuous.apply(Eq[-1])

    Eq.is_differentiable = algebra.all.then.all.limits.restrict.apply(Eq[-1], Interval(a, b, left_open=True, right_open=True))

    Eq.le = Element(t, Interval(a, b, left_open=True)).this.apply(sets.el_interval.then.le)

    Eq <<= algebra.cond.infer.then.infer.et.rhs.apply(Eq.is_continuous, Eq.le), algebra.cond.infer.then.infer.et.rhs.apply(Eq.is_differentiable, Eq.le)

    Eq <<= Eq[-2].this.rhs.apply(algebra.le.all.then.all.limits.restrict), Eq[-1].this.rhs.apply(algebra.le.all.then.all.limits.restrict)

    Eq <<= Element(t, Interval(a, b, left_open=True)).this.apply(sets.el_interval.then.lt) & Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(calculus.lt.is_continuous.is_differentiable.then.any.eq.mean_value_theorem.Lagrange)

    Eq << Eq[-1].this.rhs.apply(algebra.any.then.any.et.limits.cond, simplify=None)

    Eq << Eq[-1].this.rhs.find(Element).apply(sets.el.then.ne_empty, simplify=None)

    Eq.any = Eq[-1].this.rhs.find(Unequal).apply(sets.interval_ne_empty.then.gt_zero, simplify=None)

    Eq << algebra.cond.infer.then.infer.et.rhs.apply(Eq[1], Eq.le)

    Eq << Eq[-1].this.rhs.apply(algebra.le.all.then.all.limits.restrict)

    Eq << Eq[-1].this.find(All).apply(algebra.all.then.all.limits.restrict, Interval(a, t, left_open=True, right_open=True))

    Eq <<= Eq.any & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(algebra.all.any.then.any.et)

    Eq << Eq[-1].this.rhs.apply(algebra.any_et.then.any.limits_absorb, index=1)

    Eq << Eq[-1].this.rhs.expr.apply(algebra.gt_zero.gt_zero.then.gt_zero)

    Eq << Eq[-1].this.rhs.apply(algebra.any.then.any.et.limits.unleash)

    Eq << Eq[-1].this.rhs.expr.apply(algebra.gt.eq.then.gt.trans)

    Eq << algebra.infer.then.infer.split.et.apply(Eq[-1], 1)

    Eq << algebra.infer.then.all.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(algebra.gt_zero.then.gt)




if __name__ == '__main__':
    run()
# created on 2020-04-22
# updated on 2023-04-16
