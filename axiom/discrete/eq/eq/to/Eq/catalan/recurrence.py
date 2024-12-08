from util import *


@apply
def apply(eq, eq1):
    from Axiom.Discrete.Eq.Eq.to.Gt_0.catalan import is_catalan_series
    Cn, n = is_catalan_series(eq, eq1)
    return Equal(Cn, binomial(n * 2, n) / (n + 1))


@prove
def prove(Eq):
    from Axiom import Algebra, Calculus, Discrete, Sets

    n, k = Symbol(integer=True)
    # n = Symbol(integer=True, nonnegative=True)
    C = Symbol(shape=(oo,), integer=True)
    Eq << apply(Equal(C[0], 1),
                Equal(C[n + 1], Sum[k:n + 1](C[k] * C[n - k])))

    @Function(extended_real=True)
    def g(x):
        return Sum[n:oo](C[n] * x ** n)
    x = Symbol(domain=Interval(0, S.One / 4, left_open=True))
    Eq.g_definition = g(x).this.defun()

    Eq << Eq[1] * x ** n

    Eq << Algebra.Eq.to.Eq.Sum.apply(Eq[-1], (n, 0, oo))

    Eq << Calculus.Mul.Sum.eq.Sum.Sum.apply(C, C, n=n, k=k, x=x)

    Eq << Algebra.Eq.Eq.to.Eq.trans.apply(Eq[-2], Eq[-1])

    Eq << Eq.g_definition ** 2

    Eq.g_squared = Algebra.Eq.Eq.to.Eq.trans.apply(Eq[-2], Eq[-1])

    Eq << Eq.g_definition.this.rhs.apply(Algebra.Sum.eq.Add.shift)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1] - 1

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.subs.offset, 1)

    Eq << Eq.g_squared * x

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul.eq.Sum)

    Eq << Algebra.Eq.Eq.to.Eq.trans.apply(Eq[-1], Eq[-3])

    Eq << Algebra.Eq.to.Eq_0.apply(Eq[-1])

    Eq.ou = Eq[-1].apply(Algebra.Add.eq.Zero.to.And_Imply_Or_EqS_Div.quadratic, x=g(x), simplify=False)

    Eq.negative_sqrt = Eq.ou.args[0].copy(plausible=True)

    Eq.positive_sqrt = Any[x:x < S.One / 4](Eq.ou.args[1], plausible=True)

    x_quote = Symbol(domain=Interval(0, S.One / 4, left_open=True, right_open=True))
    x_var = Eq.positive_sqrt.variable
    Eq.positive_sqrt_quote = Eq.positive_sqrt.limits_subs(x_var, x_quote)

    Eq << Derivative[x_quote](Eq.positive_sqrt_quote.rhs).this.doit()

    Eq << Less(Eq[-1].rhs, 0, plausible=True)

    Eq << Eq[-1].this.lhs.subs(Eq[-2].reversed)

    Eq << Calculus.Lt_0.to.Gt.monotony.apply(Eq[-1])

    Eq << Algebra.Any_Eq.Cond.to.Any.subs.apply(Eq.positive_sqrt_quote, Eq[-1], reverse=True)

    Eq.any_gt = Algebra.Any.to.Any.limits.relax.subs.apply(Eq[-1], x_quote, x)

    Eq << Calculus.Eq.to.Eq.Grad.apply(Eq.g_definition, (x,), simplify=None)

    Eq << Eq[-1].this.rhs.apply(Calculus.Grad.eq.Sum)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.Add.split, cond={0})

    Eq.g_derivative = Eq[-1].this.rhs.apply(Algebra.Mul.eq.Sum)

    Eq << Discrete.Eq.Eq.to.Gt_0.catalan.apply(Eq[0], Eq[1])

    Eq << Eq[-1] * x ** (n - 1)

    Eq << Algebra.Gt.to.Gt.Sum.Mul.apply(Eq[-1], (n, 0, oo))

    Eq << Eq[-1].this.lhs.subs(Eq.g_derivative.reversed)

    Eq << Calculus.Gt_0.to.Le.monotony.apply(Eq[-1])

    Eq << Eq.ou.subs(x, S.One / 4)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Algebra.Cond.Any.to.Any.And.apply(Eq[-1], Eq.any_gt)

    Eq << ~Eq.positive_sqrt

    Eq << Algebra.All.to.Or.apply(Eq[-1])

    Eq << Eq[-1].subs(x_var, x)

    Eq << Eq[-1].this.find(NotElement).apply(Sets.NotIn_Interval.to.Or)

    Eq << Eq[-1].this.args[1].apply(Algebra.Ge.to.Eq.squeeze)

    Eq.all_ne = Algebra.Or.to.All.apply(Eq[-1], wrt=x)

    Eq << Eq.ou.apply(Algebra.Cond.to.And.All, cond=x < S.One / 4)

    Eq << Algebra.And.to.Cond.apply(Eq[-1], index=1)

    Eq << Algebra.All.to.Or.subs.apply(Eq[-1], Eq[-1].variable, x)

    Eq << Eq[-1].this.find(NotElement).simplify()

    Eq << Algebra.Or.to.All.apply(Eq[-1], wrt=x)

    Eq <<= Eq.all_ne & Eq[-1]

    Eq << Algebra.All_And.to.All.apply(Eq[-1], index=0)

    Eq << Algebra.All.to.Or.apply(Eq[-1])

    Eq << Algebra.Cond.to.All.apply(Eq[-1], x)

    Eq << Algebra.All.to.Or.apply(Eq[-1])

    Eq << Eq.negative_sqrt.apply(Algebra.Cond.of.And.All, cond=x < S.One / 4)

    Eq << Algebra.And.of.And.apply(Eq[-1])

    Eq << Algebra.All.of.Or.apply(Eq[-1])

    Eq << Eq[-1].this.args[1].apply(Sets.NotIn.of.Or.Interval)

    Eq << Calculus.Pow.eq.Sum.Binom.apply((1 - 4 * x) ** (S.One / 2), n=n)

    Eq << Eq[-1].this.rhs().find(Binomial).apply(Discrete.Binom.eq.Mul.half)

    Eq << Eq[-1].this.rhs.args[1].expr.powsimp()

    Eq << Eq[-1].this.rhs.args[1].apply(Algebra.Sum.eq.Add.shift)

    Eq << 1 - Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.subs.offset, 1)

    Eq << Eq[-1] / (x * 2)

    Eq << Eq[-1] + Eq.negative_sqrt

    Eq << Eq[-1].this.find(Mul).apply(Algebra.Mul.distribute)

    Eq << Eq[-1].this.find(Mul).apply(Algebra.Div.cancel, 2)

    Eq << Eq[-1].this.find(Binomial).apply(Discrete.Binom.eq.Div.Binom.decrease)

    Eq << Eq[-1].this.find(Binomial).apply(Discrete.Binom.eq.Div.Binom)

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul.eq.Sum)

    Eq << Eq[-1].this.rhs.expr.ratsimp()

    Eq << Algebra.Eq.Eq.to.Eq.trans.apply(Eq[-1], Eq.g_definition)

    Eq << Calculus.Eq.to.Eq.series.oo.coefficient.apply(Eq[-1].reversed, x=x)


if __name__ == '__main__':
    run()

# created on 2020-10-21
# updated on 2023-06-03
