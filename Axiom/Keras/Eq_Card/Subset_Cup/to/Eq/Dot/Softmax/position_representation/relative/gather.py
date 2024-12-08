from util import *


@apply
def apply(eq_cup, subset, Q, K, V, K_quote, V_quote):
    cup, m = eq_cup.of(Equal[Card])
    (d, j), j_limit = cup.of(Cup[FiniteSet[Indexed]])
    S[j], S[0], S[m] = j_limit
    n, d_z = Q.shape
    S[cup], (S[0], S[n]) = subset.of(Subset[Expr, Range])
    return Equal(softmax(Q @ (K + K_quote).T / sqrt(d_z) + (Lamda[j:n](Bool(Element(j, cup))) - OneMatrix(n, n)) * oo) @ (V + V_quote), \
                 softmax(Q @ (Lamda[j:m](K[d[j]]).T + Transpose[0, 2](Lamda[j:m](K_quote[:, d[j]]))) / sqrt(d_z)) @ (Lamda[j:m](V[d[j]]) + Transpose[0, 1](Lamda[j:m](V_quote[:, d[j]]))))


@prove
def prove(Eq):
    from Axiom import Keras, Algebra, Sets, Discrete

    n, k, m = Symbol(integer=True, positive=True)
    r = Symbol(shape=(n,), integer=True)
    d_z = Symbol(integer=True, positive=True)
    Q = Symbol(shape=(n, d_z), real=True)
    K = Symbol(shape=(n, d_z), real=True)
    V = Symbol(shape=(n, d_z), real=True)
    d = Symbol(shape=(oo,), integer=True)
    i, j = Symbol(integer=True)
    K_quote = Symbol(shape=(n, n, d_z), real=True)
    V_quote = Symbol(shape=(n, n, d_z), real=True)
    s = d[:m].cup_finiteset(j)
    Eq << apply(
        Equal(Card(s), m),
        Subset(s, Range(n)),
        Q, K, V, K_quote, V_quote)

    a = Symbol(Eq[-1].find(Mul[MatMul]))
    Eq.a_def = a.this.definition

    z = Symbol(Eq[2].lhs)
    Eq.z_def = z.this.definition

    Eq << Eq.z_def[i]

    Xi = Symbol(Eq[-1].find(Lamda))
    Eq.Xi_def = Xi.this.definition

    Eq << Eq[-1].this.rhs.subs(Eq.Xi_def.reversed, Eq.a_def[i].reversed)

    Eq << Eq[-1].this.find(softmax).apply(Keras.Softmax.eq.Mul.ReducedSum)

    Eq << Algebra.Mul.eq.Exp.oo.apply(exp(a[i]) * Xi).reversed

    Eq.zi_definition = Eq[-2].subs(Eq[-1])

    Eq << Eq.zi_definition.find(ReducedSum).this.subs(Eq.Xi_def)

    Eq << Eq[-1].this.rhs.apply(Algebra.ReducedSum.eq.Sum, j)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.absorb)

    Eq.eq_intersect = Sets.Subset.to.Eq.Intersect.apply(Eq[1])

    Eq << Eq[-1].subs(Eq.eq_intersect)

    Eq << Sets.Eq_Card.to.Eq.ReducedSum.apply(Eq[0], Eq[-1].find(Sum))

    Eq << Algebra.Eq.Eq.to.Eq.trans.apply(Eq[-2], Eq[-1])

    Eq.zi_definition = Eq.zi_definition.subs(Eq[-1])

    Eq << Eq.zi_definition.find(MatMul).this.apply(Discrete.Dot.eq.Lamda)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.limits.domain_defined)

    k = Eq[-1].rhs.expr.variable
    Eq << Eq.Xi_def[k]

    Eq << Eq[-2].this.rhs.subs(Eq[-1])

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.limits.absorb)

    Eq << Eq[-1].subs(Eq.eq_intersect)

    Eq << Sets.Eq_Card.to.Eq.Sum.apply(Eq[0], Eq[-1].find(Sum))

    Eq << Eq[-1].this.rhs.apply(Discrete.Sum.eq.Dot)

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Eq[-1].this.rhs.expr.T

    Eq << Eq[-1].this.rhs.apply(Discrete.Lamda.Dot.eq.Dot)

    Eq << Eq.zi_definition.subs(Eq[-1])

    Eq << Eq[-1].this.find(Lamda).apply(Keras.Lamda.Exp.eq.Mul.Softmax)

    Eq << Eq[-1].subs(Eq.a_def)

    Eq << Eq[-1].this.find(Lamda[Mul]).apply(Algebra.Lamda.eq.Mul)

    Eq << Eq[-1].this.find(Lamda[MatMul]).apply(Discrete.Lamda.Dot.eq.Dot)

    Eq << Eq[-1].this.find(Lamda[Tuple[2]]).apply(Algebra.Lamda.eq.Transpose)

    Eq << Algebra.Eq.to.Eq.Lamda.apply(Eq[-1], (i, 0, n))

    Eq << Eq[-1].this.rhs.apply(Discrete.Lamda.Dot.eq.Dot)

    Eq << Eq[-1].this.find(Lamda).apply(Keras.Lamda.Softmax.eq.Softmax)

    Eq << Eq[-1].this.find(Lamda[MatMul]).apply(Discrete.Lamda.Dot.eq.Dot)

    Eq << Eq[-1].this.find(Transpose[Lamda]).apply(Algebra.Transpose.eq.Lamda)

    Eq << Eq[-1].this.find(Lamda[Add]).apply(Algebra.Lamda.eq.Add)

    Eq << Eq[-1].this.find(Add[~Lamda[Tuple[2]]]).apply(Algebra.Lamda.eq.Transpose, axis=(0, 1))

    Eq << Eq[-1].this.find(Lamda[Add]).apply(Algebra.Lamda.eq.Add)

    Eq << Eq[-1].this.find(Lamda[Tuple[2]]).apply(Algebra.Lamda.eq.Transpose)

    Eq << Eq[-1].this.find(Lamda[Tuple[3]]).apply(Algebra.Lamda.eq.Transpose)

    Eq << Eq[-1].this.find(Lamda[Tuple[2]]).apply(Algebra.Lamda.eq.Transpose, axis=(0, 1))

    Eq << Algebra.Eq.Eq.to.Eq.trans.apply(Eq.z_def, Eq[-1])


if __name__ == '__main__':
    run()
# created on 2022-01-11
# updated on 2023-03-19
