from util import *


@apply
def apply(is_limited):
    from Axiom.Calculus.is_limited.to.Any.All.limit_definition import of_limited
    fx, (x, x0) = of_limited(is_limited, nonzero=True)

    return Equal(Limit[x:x0](1 / fx), 1 / is_limited.lhs)


@prove
def prove(Eq):
    from Axiom import Calculus, Sets, Algebra

    x, x0 = Symbol(real=True)
    g = Function(real=True)
    Eq << apply(Element(Limit[x:x0](g(x)), Reals - {0}))

    ε_0 = Symbol(real=True, positive=True)
    δ_0 = Symbol(real=True, positive=True)
    Eq << Calculus.is_limited.to.Any.All.limit_definition.symbol_subs.apply(Eq[0], ε_0, δ_0, var='A')

    A = Eq[-1].find(Abs[Add[-~Symbol]])
    Eq.is_limited = A.this.definition.reversed

    Eq.is_nonzero_real = Eq[0].subs(Eq.is_limited)

    Eq << Sets.In.to.Ne_0.apply(Eq.is_nonzero_real)

    Eq << Algebra.Ne_0.Eq.to.Eq.Inv.apply(Eq[-1], Eq.is_limited)

    Eq << Eq[1].subs(Eq[-1])

    Eq << Algebra.And.of.And.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq.is_limited)

    δ_1 = Symbol(positive=True)
    Eq << Calculus.Eq_Limit.In.to.Any.All.Lt.half.apply(Eq.is_limited, Eq.is_nonzero_real, delta=δ_1)

    Eq.A_is_positive = Sets.is_nonzero.to.Gt_0.Abs.apply(Eq.is_nonzero_real)

    Eq << Algebra.Cond.Any_All.to.Any.All.And.apply(Eq.A_is_positive / 2, Eq[-1])

    Eq << Eq[-1].this.expr.expr.apply(Algebra.Gt_0.Gt.to.Lt.Inv)

    Eq << Algebra.Gt_0.to.Gt_0.Div.apply(Eq.A_is_positive)

    Eq << Algebra.Cond.Any_All.to.Any.All.And.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.expr.expr.apply(Algebra.Gt_0.Lt.to.Lt.Mul)

    Eq << Algebra.Any_All.Any_All.to.Any.All.And.limits_Intersect.apply(Eq[2], Eq[-1])

    Eq << Eq[-1].this.expr.expr.apply(Algebra.Lt.Lt.to.Lt.Mul)

    Eq << Eq[-1].this.find(Mul[Abs]).apply(Algebra.Mul.eq.Abs)

    Eq << Eq[-1].this.find(Abs[~Mul]).apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.expr.expr.lhs.apply(Algebra.Abs.Neg)

    Eq << Eq[-1].this.expr.limits[0][1].args[0].apply(Sets.Lt.of.In.Interval)

    Eq << Eq[-1].this.expr.limits[0][1].args[0].apply(Sets.Lt.of.In.Interval)

    Eq << Eq[-1].this.expr.limits[0][1].args[1].simplify()

    ε, δ = Symbol(positive=True)
    Eq << Algebra.Cond.to.Or.subs.apply(Eq[-1], ε_0, abs(A) ** 2 / 2 * ε)

    Eq << Algebra.Gt_0.to.Gt_0.Square.apply(Eq.A_is_positive) * ε / 2

    Eq << Algebra.Cond.Or.to.Cond.apply(Eq[-1], Eq[-2])

    Eq << Algebra.Any.to.Any.subs.apply(Eq[-1], Min(δ_0, δ_1), δ)

    Eq << Calculus.Any_All.to.Eq.limit_definition.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-06-18
# updated on 2023-04-16