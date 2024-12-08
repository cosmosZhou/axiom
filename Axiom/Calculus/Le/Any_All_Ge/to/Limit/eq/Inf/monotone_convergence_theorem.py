from util import *


@apply
def apply(le, Any_All_Ge):

    ((an, M), (n, S[0], S[oo])), (S[M],) = Any_All_Ge.of(Any[All[GreaterEqual]])
    S[an._subs(n, n + 1)], S[an] = le.of(LessEqual)
    return Equal(Limit[n:oo](an), Inf[n:oo](an))


@prove
def prove(Eq):
    from Axiom import Algebra, Sets, Calculus

    a = Symbol(real=True, shape=(oo,), given=True)
    n = Symbol(integer=True)
    M = Symbol(real=True)
    Eq << apply(a[n + 1] <= a[n], Exists[M](ForAll[n:oo](a[n] >= M)))

    N = Symbol(integer=True, nonnegative=True)
    epsilon = Symbol(real=True, positive=True)
    Eq.any_lt = Exists[N](a[N] < Eq[2].find(Inf) + epsilon, plausible=True)

    Eq << ~Eq.any_lt

    Eq << Eq[-1].this.expr.apply(Algebra.All_Ge.to.GeInf)

    Eq.any_ge = Eq[-1].this.find(Inf).limits_subs(N, n)

    Eq << Eq[1].this.expr.apply(Algebra.All_Ge.to.GeInf)

    Eq << Eq[-1].this.expr.apply(Algebra.Ge.to.Gt.relax, lower=-oo)

    Eq.le_inf = Algebra.All_LeInf.apply(Eq[-1].lhs)

    Eq << Algebra.Le.to.Lt.relax.apply(Eq.le_inf, upper=oo)

    Eq.inf_is_real = Sets.Gt.Lt.to.In.Interval.apply(Eq[-2], Eq[-1], simplify=None)

    Eq << Algebra.Cond.Any.to.Any.And.apply(Eq.inf_is_real, Eq.any_ge, simplify=None)

    Eq << Eq[-1].this.expr.apply(Sets.Ge.In.to.Ge.Sub)

    Eq << Eq.any_lt.this.expr - epsilon

    Eq << Eq[-1].this.expr.reversed

    Eq << -Eq[-1].this.expr

    Eq.any_gt = Eq[-1].this.expr + a[N]

    Eq << Algebra.Le.to.All.Le.monotone.apply(Eq[0], n, N)

    Eq << Algebra.All.to.All.limits.restrict.apply(Eq[-1], domain=Range(N + 1, oo))

    Eq << Algebra.Cond.All.to.All.And.apply(Eq.inf_is_real, Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.apply(Sets.Le.In.to.Le.Sub)

    Eq << Algebra.All.Any.to.Any.All.And.apply(Eq[-1], Eq.any_gt)

    Eq << Eq[-1].this.expr.expr.apply(Algebra.Lt.Le.to.Lt.trans)

    Eq << Algebra.Le.to.Eq.Abs.apply(Eq.le_inf)

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.find(Abs).apply(Algebra.Abs.Neg)

    Eq << Calculus.Any_All.to.Eq.limit_definition.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-06-24
