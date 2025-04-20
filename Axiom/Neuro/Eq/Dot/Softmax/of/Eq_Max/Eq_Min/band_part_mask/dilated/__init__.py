from util import *


@apply
def apply(eq_max, eq_min, A, V):
    (((i, l), (S[i - l + 1], d)), i_limit), β = eq_max.of(Equal[Lamda[Max[Expr + 1 - Expr, Mod]]])
    S[i], S[0], n = i_limit

    ((S[n], (S[i], u)), S[i_limit]), ζ = eq_min.of(Equal[Lamda[Min[Add]]])

    S[n], S[n] = A.shape

    indices = slice(β[i], ζ[i], d)

    return Equal(softmax(A + (BandPart[l - 1, u - 1, d](OneMatrix(n, n)) - 1) * oo) @ V, Lamda[i:n](softmax(A[i, indices]) @ (V[indices])))


@prove
def prove(Eq):
    from Axiom import Neuro, Algebra, Set, Discrete, Logic

    n, l, u, d_z, d = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    A = Symbol(real=True, shape=(n, n))
    V = Symbol(real=True, shape=(n, d_z))
    β, ζ = Symbol(shape=(n,), integer=True)
    (Eq.beta, Eq.zeta), Eq.objective = apply(Equal(β, Lamda[i:n](Max(i - l + 1, (i - l + 1) % d))), Equal(ζ, Lamda[i:n](Min(i + u, n))), A, V)

    band_part = Eq.objective.find(BandPart)
    Eq << Algebra.Mul.eq.Exp.Infty.apply(exp(A) * band_part).reversed

    a_quote = Symbol(Eq[-1].lhs.arg)
    Eq.a_quote_def = a_quote.this.definition

    Eq << Eq[-1].subs(Eq.a_quote_def.reversed)

    Xi = Symbol(band_part)
    Eq.Xi_definition = Xi.this.definition

    Eq << Eq[-1].subs(Eq.Xi_definition.reversed)

    Eq << Eq[-1][i]

    z = Symbol(Eq.objective.lhs)
    Eq.z_definition = z.this.definition

    Eq << Eq.z_definition.subs(Eq.a_quote_def.reversed)

    Eq << Eq[-1][i]

    Eq << Eq[-1].this.rhs.args[0].apply(Neuro.Softmax.eq.Mul.ReducedSum)

    Eq.zi_definition = Eq[-1].this.rhs.subs(Eq[-4])

    Eq << Eq.Xi_definition.this.rhs.defun()

    Eq << Eq[-1][i]

    Eq.Xi_definition = Eq[-1].this.rhs.expr.apply(Logic.Bool.eq.Ite)

    Eq << Eq.zi_definition.rhs.args[-1].args[0].this.arg.args[0].subs(Eq.Xi_definition)

    Eq << Eq[-1].this.rhs.apply(Algebra.ReducedSum.eq.Sum)

    Eq << Eq[-1].this.find(Element).apply(Set.Mem_Icc.Is.MemAdd, i)

    Eq << Eq[-1].subs(Eq.beta[i].reversed, Eq.zeta[i].reversed)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.ReducedSum)

    Eq.zi_definition = Eq.zi_definition.subs(Eq[-1])

    Eq << Eq.zi_definition.rhs.args[0].this.apply(Discrete.Dot.eq.Lamda)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.limits.domain_defined)

    k = Eq[-1].rhs.expr.variable
    Eq << Eq.Xi_definition[k]

    Eq << Eq[-2].this.rhs.expr.expr.subs(Eq[-1])

    Eq << Eq[-1].subs(Eq.beta[i].reversed, Eq.zeta[i].reversed)

    Eq << Eq[-1].this.rhs.expr.apply(Discrete.Sum.eq.Dot)

    Eq << Eq[-1].this.rhs.expr.T

    Eq << Eq[-1].this.rhs.apply(Discrete.Lamda.Dot.eq.Dot)

    Eq << Eq.zi_definition.this.rhs.subs(Eq[-1])

    Eq << Eq[-1].this.find(exp).apply(Neuro.Exp.eq.Mul.Softmax)

    Eq << Algebra.EqLamda.of.Eq.apply(Eq[-1], (i, 0, n))

    Eq << Algebra.Eq.of.Eq.Eq.apply(Eq.z_definition, Eq[-1])





if __name__ == '__main__':
    run()
# created on 2021-12-26# updated on 2022-01-01# updated on 2022-01-01# updated on 2022-01-01# updated on 2022-01-01# updated on 2022-01-01# updated on 2022-01-01# updated on 2022-01-01
# updated on 2022-03-30


from . import bert
