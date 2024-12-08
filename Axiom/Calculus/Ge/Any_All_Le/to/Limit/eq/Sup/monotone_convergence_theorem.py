from util import *


@apply
def apply(ge, Any_All_Le):
    ((an, M), (n, S[0], S[oo])), (S[M],) = Any_All_Le.of(Any[All[LessEqual]])
    S[an._subs(n, n + 1)], S[an] = ge.of(GreaterEqual)
    return Equal(Limit[n:oo](an), Sup[n:oo](an))


@prove
def prove(Eq):
    from Axiom import Algebra, Sets, Calculus

    a = Symbol(real=True, shape=(oo,), given=True)
    n = Symbol(integer=True)
    M = Symbol(real=True)
    Eq << apply(a[n + 1] >= a[n], Exists[M](ForAll[n:oo](a[n] <= M)))

    N = Symbol(integer=True, nonnegative=True)
    epsilon = Symbol(real=True, positive=True)
    Eq.any_gt = Exists[N](a[N] > Eq[2].find(Sup) - epsilon, plausible=True)

    Eq << ~Eq.any_gt

    Eq << Eq[-1].this.expr.apply(Algebra.All_Le.to.LeSup)

    Eq.any_le = Eq[-1].this.find(Sup).limits_subs(N, n)

    Eq << Eq[1].this.expr.apply(Algebra.All_Le.to.LeSup)

    Eq << Eq[-1].this.expr.apply(Algebra.Le.to.Lt.relax, upper=oo)

    Eq.ge_sup = Algebra.All_GeSup.apply(Eq[-1].lhs)

    Eq << Algebra.Ge.to.Gt.relax.apply(Eq.ge_sup, lower=-oo)

    Eq.sup_is_real = Sets.Lt.Gt.to.In.Interval.apply(Eq[-2], Eq[-1], simplify=None)

    Eq << Algebra.Cond.Any.to.Any.And.apply(Eq.sup_is_real, Eq.any_le, simplify=None)

    Eq << Eq[-1].this.expr.apply(Sets.Le.In.to.Le.Sub)

    Eq << Eq.any_gt.this.expr + epsilon

    Eq << Eq[-1].this.expr.reversed

    Eq.any_lt = Eq[-1].this.expr - a[N]

    Eq << Algebra.Ge.to.All.Ge.monotone.apply(Eq[0], n, N)

    Eq << Algebra.All.to.All.limits.restrict.apply(Eq[-1], domain=Range(N + 1, oo))

    Eq << -Eq[-1].this.expr

    Eq << Algebra.Cond.All.to.All.And.apply(Eq.sup_is_real, Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.apply(Sets.Le.In.to.Le.Add)

    Eq << Algebra.All.Any.to.Any.All.And.apply(Eq[-1], Eq.any_lt)

    Eq << Eq[-1].this.expr.expr.apply(Algebra.Lt.Le.to.Lt.trans)

    Eq << Algebra.Ge.to.Eq.Abs.apply(Eq.ge_sup)

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.find(Abs).apply(Algebra.Abs.Neg)

    Eq << Calculus.Any_All.to.Eq.limit_definition.apply(Eq[-1])

    # https://en.wikipedia.org/wiki/Least-upper-bound_property
    # https://en.wikipedia.org/wiki/Monotone_convergence_theorem




if __name__ == '__main__':
    run()
# created on 2020-05-20
# updated on 2023-11-11
