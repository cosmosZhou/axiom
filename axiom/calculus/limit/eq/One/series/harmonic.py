from util import *


@apply
def apply(n):
    k = Symbol(integer=True)
    return Equal(Limit[n:oo](Sum[k:1:n](1 / k) / log(n + 1)), 1)


@prove
def prove(Eq):
    from Axiom import Algebra, Calculus, Sets

    n = Symbol(integer=True, positive=True)
    Eq << apply(n)

    x = Symbol(real=True)
    x0 = Symbol(real=True, positive=True)
    Eq.is_continuous = Equal(Limit[x:x0](1 / x), 1 / x0, plausible=True)

    Eq << Eq.is_continuous.this.lhs.doit()

    k, *ab = Eq[-1].lhs.args[0].args[-1].limits[0]
    k = k.copy(domain=Range(*ab))
    Eq << Eq.is_continuous.apply(Algebra.Cond.to.All.restrict, (x0, Interval(k, k + 1)))

    Eq.mean_value_theorem = Calculus.is_continuous.to.Any.Eq.mean_value_theorem.apply(Eq[-1])

    Eq << Algebra.All.limits_assert.apply(Eq[-1].limits)

    Eq << Eq[-1].this.expr.apply(Sets.In.to.In.Inv.Interval)

    Eq << Eq[-1].this.expr.apply(Sets.In_Interval.to.And)

    Eq << Algebra.All_And.to.And.All.apply(Eq[-1])

    Eq <<= Algebra.All.Any.to.Any.And.apply(Eq[-2], Eq.mean_value_theorem), Algebra.All.Any.to.Any.And.apply(Eq[-1], Eq.mean_value_theorem)

    Eq <<= Eq[-2].this.expr.apply(Algebra.Eq.Cond.to.Cond.subs, reverse=True), \
    Eq[-1].this.expr.apply(Algebra.Eq.Cond.to.Cond.subs, reverse=True)

    Eq <<= Eq[-2].apply(Algebra.Cond.to.All.restrict, (k, 1, n)), Eq[-1].apply(Algebra.Cond.to.All.restrict, (k, 1, n - 1))

    Eq <<= Algebra.All_Le.to.Le.Sum.apply(Eq[-2]), Algebra.All_Ge.to.Ge.Sum.apply(Eq[-1])

    Eq <<= Eq[-2].this.lhs.doit(), Eq[-1].this.lhs.doit().reversed

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.limits.subs.offset, -1) + 1

    Eq <<= Eq[-3] / Eq[-3].lhs, Eq[-1] / Eq[-3].lhs

    Eq <<= Calculus.Le.to.Le.Limit.apply(Eq[-2], (n, oo)), Calculus.Le.to.Le.Limit.apply(Eq[-1], (n, oo))

    Eq << Eq[-1].this.rhs.doit()

    Eq <<= Eq[-1] & Eq[-3]


if __name__ == '__main__':
    run()

# created on 2020-06-25
