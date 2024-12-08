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
    from Axiom import Sets, Calculus, Algebra

    a, b = Symbol(real=True, given=True)
    domain = Interval(a, b)
    x, t = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(a < b, All[x:domain](Derivative[x](f(x)) > 0))

    Eq << Eq[1].this.expr.apply(Sets.Gt_0.to.is_real)

    Eq.is_continuous = Calculus.is_differentiable.to.is_continuous.apply(Eq[-1])

    Eq.is_differentiable = Algebra.All.to.All.limits.restrict.apply(Eq[-1], Interval(a, b, left_open=True, right_open=True))

    Eq.le = Element(t, Interval(a, b, left_open=True)).this.apply(Sets.In_Interval.to.Le)

    Eq <<= Algebra.Cond.Imply.to.Imply.And.rhs.apply(Eq.is_continuous, Eq.le), Algebra.Cond.Imply.to.Imply.And.rhs.apply(Eq.is_differentiable, Eq.le)

    Eq <<= Eq[-2].this.rhs.apply(Algebra.Le.All.to.All.limits.restrict), Eq[-1].this.rhs.apply(Algebra.Le.All.to.All.limits.restrict)

    Eq <<= Element(t, Interval(a, b, left_open=True)).this.apply(Sets.In_Interval.to.Lt) & Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(Calculus.Lt.is_continuous.is_differentiable.to.Any.Eq.mean_value_theorem.Lagrange)

    Eq << Eq[-1].this.rhs.apply(Algebra.Any.to.Any.And.limits.Cond, simplify=None)

    Eq << Eq[-1].this.rhs.find(Element).apply(Sets.In.to.Ne_EmptySet, simplify=None)

    Eq.any = Eq[-1].this.rhs.find(Unequal).apply(Sets.Interval_Ne_EmptySet.to.Gt_0, simplify=None)

    Eq << Algebra.Cond.Imply.to.Imply.And.rhs.apply(Eq[1], Eq.le)

    Eq << Eq[-1].this.rhs.apply(Algebra.Le.All.to.All.limits.restrict)

    Eq << Eq[-1].this.find(All).apply(Algebra.All.to.All.limits.restrict, Interval(a, t, left_open=True, right_open=True))

    Eq <<= Eq.any & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Algebra.All.Any.to.Any.And)

    Eq << Eq[-1].this.rhs.apply(Algebra.Any_And.to.Any.limits_absorb, index=1)

    Eq << Eq[-1].this.rhs.expr.apply(Algebra.Gt_0.Gt_0.to.Gt_0)

    Eq << Eq[-1].this.rhs.apply(Algebra.Any.to.Any.And.limits.unleash)

    Eq << Eq[-1].this.rhs.expr.apply(Algebra.Gt.Eq.to.Gt.trans)

    Eq << Algebra.Imply.to.Imply.split.And.apply(Eq[-1], 1)

    Eq << Algebra.Imply.to.All.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(Algebra.Gt_0.to.Gt)




if __name__ == '__main__':
    run()
# created on 2020-04-22
# updated on 2023-04-16
