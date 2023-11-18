from util import *


@apply
def apply(le, is_positive, w=None):
    x0, x1 = le.of(LessEqual)
    fx, (x_, S[2]) = is_positive.of(Derivative > 0)

    if w is None:
        w = Symbol(domain=Interval(0, 1))
    else:
        assert 0 <= w <= 1
    domain = x_.domain
    assert domain.left_open and domain.right_open

    return GreaterEqual(w * fx._subs(x_, x0) + (1 - w) * fx._subs(x_, x1), fx._subs(x_, w * x0 + (1 - w) * x1))


@prove
def prove(Eq):
    from axiom import calculus, algebra, sets

    a, b = Symbol(real=True, given=True)
    domain = Interval(a, b, left_open=True, right_open=True)
    x = Symbol(domain=domain)
    f = Function(real=True)
    x0, x1 = Symbol(domain=domain, given=True)
    w = Symbol(domain=Interval(0, 1), given=True)
    Eq << apply(x0 <= x1, Derivative(f(x), (x, 2)) > 0, w=w)

    (w, fx0), (_w, fx1) = Eq[-1].lhs.of(Mul + Mul)
    x0 = fx0.arg
    x1 = fx1.arg
    Eq << calculus.gt_zero.imply.is_differentiable.within.apply(Eq[1], x0, x1)

    Eq << calculus.is_differentiable.imply.is_continuous.apply(Eq[-1])

    Eq << calculus.le.is_continuous.is_differentiable.imply.any.eq.mean_value_theorem.Lagrange.close.apply(Eq[0], Eq[-1], Eq[-2])

    Eq << Eq[-1].this.expr * w

    Eq.is_nonpositive = Eq[0] - x1

    Eq <<= algebra.le.imply.le.mul.apply(Eq.is_nonpositive, w) + x1, algebra.ge.imply.ge.mul.apply(Eq[0].reversed, 1 - w) + w * x0

    Eq << Eq[-2].this.find(Mul).apply(algebra.mul.to.add, simplify=None)

    Eq.ge = Eq[-2].this.rhs.find(Mul[Add]).apply(algebra.mul.to.add, simplify=None)

    Eq.le = Eq[-1].this.lhs.apply(algebra.add.collect, factor=x1)

    Eq.all_is_positive = algebra.cond.imply.all.apply(Eq[1], x)

    Eq.x0_contains, Eq.x1_contains = Element(x0, domain, plausible=True), Element(x1, domain, plausible=True)

    Eq.x_mean_contains = sets.el.el.imply.el.interval.apply(Eq.x0_contains, Eq.x1_contains, w)

    Eq <<= calculus.el.el.all_gt_zero.imply.is_differentiable.apply(Eq.x0_contains, Eq.x_mean_contains, Eq.all_is_positive), calculus.el.el.all_gt_zero.imply.is_differentiable.apply(Eq.x_mean_contains, Eq.x1_contains, Eq.all_is_positive)

    x_ = Symbol("x'", real=True)
    Eq << Eq[-2].limits_subs(Eq[-2].variable, x_)

    x__ = Symbol("x''", real=True)
    Eq << Eq[-1].limits_subs(Eq[-1].variable, x__)

    Eq <<= calculus.is_differentiable.imply.is_continuous.apply(Eq[-2]), calculus.is_differentiable.imply.is_continuous.apply(Eq[-1])

    Eq <<= calculus.le.is_continuous.is_differentiable.imply.any.eq.mean_value_theorem.Lagrange.close.apply(Eq.ge.reversed, Eq[-2], Eq[-4]), calculus.le.is_continuous.is_differentiable.imply.any.eq.mean_value_theorem.Lagrange.close.apply(Eq.le, Eq[-1], Eq[-3])

    Eq <<= Eq[-2].this.expr.rhs.args[0].apply(algebra.add.collect), Eq[-1].this.expr.rhs.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq <<= Eq[-2].this.expr.rhs.args[0].apply(algebra.add.collect, factor=1 - w), Eq[-1].this.expr.rhs.find(Add[Mul]).apply(algebra.add.to.mul)

    Eq <<= Eq[-2].this.expr * w, Eq[-1].this.expr * (1 - w)

    Eq << algebra.any.any.imply.any.et.apply(Eq[-2], Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.eq.eq.imply.eq.sub, swap=True)


    Eq << Eq[-1].this.expr.lhs.find(Mul[Add]).apply(algebra.mul.to.add)
    Eq << Eq[-1].this.expr.lhs.find(Mul[Add]).apply(algebra.mul.to.add)
    Eq << Eq[-1].this.expr.lhs.find(Mul[Add]).apply(algebra.mul.to.add)
    Eq << Eq[-1].this.expr.lhs.apply(algebra.add.collect, factor=f(x1))
    Eq.any = Eq[-1].this.expr.rhs.apply(algebra.add.collect, factor=w * (1 - w) * (x1 - x0))
    Eq.suffice = Eq.any.limits_cond.this.apply(sets.el.el.imply.le)
    Eq <<= sets.el.el.imply.subset.interval.apply(Eq.x0_contains, Eq.x_mean_contains), sets.el.el.imply.subset.interval.apply(Eq.x_mean_contains, Eq.x1_contains)
    Eq <<= algebra.cond.imply.infer.apply(Eq[-2], cond=Eq.suffice.lhs.args[0]), algebra.cond.imply.infer.apply(Eq[-1], cond=Eq.suffice.lhs.args[1])
    Eq <<= algebra.infer_et.imply.infer.et.apply(Eq[-2]), algebra.infer_et.imply.infer.et.apply(Eq[-1])
    Eq <<= Eq[-2].this.rhs.apply(sets.el.subset.imply.el), Eq[-1].this.rhs.apply(sets.el.subset.imply.el)
    Eq << algebra.infer.infer.imply.infer.et.apply(Eq[-2], Eq[-1])
    Eq << algebra.cond.imply.infer.apply(Eq.all_is_positive, cond=Eq[-1].lhs)
    Eq <<= Eq[-1] & Eq[-2] & Eq.suffice
    Eq << Eq[-1].this.rhs.apply(calculus.le.el.el.all_gt_zero.imply.le)
    Eq.is_nonnegative = Eq[-1].this.rhs.apply(algebra.le.imply.ge_zero)
    Eq << GreaterEqual(w * (1 - w), 0, plausible=True)
    Eq << algebra.ge_zero.ge_zero.imply.ge_zero.apply(Eq[-1], -Eq.is_nonpositive)
    Eq << algebra.cond.imply.infer.apply(Eq[-1], cond=Eq[-3].lhs)
    Eq <<= Eq[-1] & Eq.is_nonnegative
    Eq <<= Eq[-1].this.rhs.apply(algebra.ge_zero.ge_zero.imply.ge_zero)
    Eq << algebra.infer.imply.all.apply(Eq[-1], wrt=(x_, x__))
    Eq << algebra.all.any.imply.any.et.apply(Eq[-1], Eq.any)
    Eq << Eq[-1].this.expr.apply(algebra.ge.eq.imply.ge.transit)
    Eq << algebra.et.imply.et.apply(Eq[-1])
    Eq << Eq[-1] + Eq[2].rhs




if __name__ == '__main__':
    run()
# created on 2020-05-11
# updated on 2023-05-18
