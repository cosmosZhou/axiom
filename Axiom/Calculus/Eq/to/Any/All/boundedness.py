from util import *


@apply
def apply(given, M=None):
    lim, a = given.of(Equal)
    expr, (n, *_) = lim.args
    assert n.is_integer
    if M is None:
        M = Symbol(positive=True)
    else:
        assert M.domain == Interval.open(0, oo)
    return Any[M](All[n](abs(expr) <= M))


@prove
def prove(Eq):
    from Axiom import Calculus, Algebra, Sets

    n = Symbol(integer=True)
    x = Symbol(real=True, shape=(oo,), given=True)
    a = Symbol(real=True, given=True)
    Eq << apply(Equal(Limit[n:oo](x[n]), a))

    Eq << Calculus.Eq_Limit.to.Any.All.limit_definition.apply(Eq[0])

    ε = Eq[-1].expr.expr.rhs
    Eq << Eq[-1].this.expr.expr.apply(Algebra.Lt.to.Lt.Abs.Max)

    Eq.lt = Eq[-1].subs(ε, S.Half)

    N = Eq.lt.variable
    a_max = Eq.lt.expr.expr.rhs
    M = Symbol(Max(a_max, Maxima[n:N + 1](abs(x[n]))))
    Eq << M.this.definition

    Eq << LessEqual(a_max, M, plausible=True)

    Eq << Eq[-1].this.rhs.definition

    Eq << Eq.lt.this.expr.expr.apply(Algebra.Lt.Le.to.Lt.trans, Eq[-1])

    Eq.less_than = Eq[-1].this.expr.expr.apply(Algebra.Lt.to.Le.relax)

    Eq << Algebra.All_GeMaxima.apply(Maxima[n:N + 1](abs(x[n])))

    Eq << LessEqual(Maxima[n:N + 1](abs(x[n])), M, plausible=True)

    Eq << Eq[-1].this.rhs.definition

    Eq << Eq[-2].this.expr.apply(Algebra.Ge.Le.to.Le.trans, Eq[-1])

    Eq.any = Algebra.Any_All.All.to.Any.All.apply(Eq.less_than, Eq[-1])

    Eq << Algebra.Any.of.Any.subs.apply(Eq[1], Eq[1].variable, M)

    Eq << Eq[-1].this.find(Element).apply(Sets.In.of.Gt_0)
    Eq << Eq[-1].this.find(All).apply(Algebra.All.limits.domain_defined)

    Eq.is_nonzero = Unequal(M, 0, plausible=True)

    Eq << Eq.is_nonzero.this.lhs.definition

    Eq << ~Eq[-1]

    Eq << Eq[-1].this.expr.apply(Algebra.Eq_Max.to.And.Ge, simplify=None)

    Eq << Eq[-1].this.expr.args[0].apply(Algebra.Le_0.to.Eq_0, simplify=None)

    Eq << Eq[-1].this.find(Equal[0]).apply(Algebra.Eq_Max.to.And.Ge, simplify=None)

    Eq << Eq[-1].this.expr.apply(Algebra.And.to.And.delete, index=-1)

    Eq << Eq[-1].this.args[0].apply(Algebra.Le_.Abs.Zero.to.Eq_0)

    Eq << Eq[-1].this.args[1].apply(Algebra.Le_.Abs.Zero.to.Eq_0)

    Eq << Eq[-1].this.apply(Algebra.Eq.Eq.to.Eq.Sub)

    Eq << GreaterEqual(M, 0, plausible=True)

    Eq << Algebra.Ne_0.Ge_0.to.Gt_0.apply(Eq.is_nonzero, Eq[-1])

    Eq << Algebra.Cond.Any.to.Any.And.apply(Eq[-1], Eq.any)





if __name__ == '__main__':
    run()

# created on 2020-05-16
# updated on 2023-11-17
