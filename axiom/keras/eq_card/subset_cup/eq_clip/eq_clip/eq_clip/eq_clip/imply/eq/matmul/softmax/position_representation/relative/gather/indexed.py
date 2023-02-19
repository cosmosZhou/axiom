from util import *


@apply
def apply(eq_cup, subset, eq_K_quote, eq_V_quote, eq_K_dquote, eq_V_dquote, Q, K, V):
    cup, m = eq_cup.of(Equal[Card])
    (d, j), j_limit = cup.of(Cup[FiniteSet[Indexed]])
    S[j], S[0], S[m] = j_limit
    n, d_z = Q.shape    
    S[cup], (S[0], S[n]) = subset.of(Subset[Expr, Range])     
    
    ((w_K, clip_index), j_limit, i_limit), K_quote = eq_K_quote.of(Equal[Lamda[Indexed]])
    ((w_V, S[clip_index]), S[j_limit], S[i_limit]), V_quote = eq_V_quote.of(Equal[Lamda[Indexed]])
    i, S[0], S[n] = i_limit
    k, (((r, S[j]), (S[r], S[i])), S[-k], S[k]) = clip_index.of(Add[clip[Indexed - Indexed]])
    S[j], S[0], S[n] = j_limit
    
    ((S[w_K], clip_index), j_limit, i_limit), K_dquote = eq_K_dquote.of(Equal[Lamda[Indexed]])
    ((S[w_V], S[clip_index]), S[j_limit], S[i_limit]), V_dquote = eq_V_dquote.of(Equal[Lamda[Indexed]])
        
    j, S[0], S[m] = j_limit
    S[k], (S[r[d[j]] - r[i]], S[-k], S[k]) = clip_index.of(Add[clip])


    return Equal(softmax(Q @ (K + K_quote).T / sqrt(d_z) + (Lamda[j:n](Bool(Element(j, cup))) - OneMatrix(n, n)) * oo) @ (V + V_quote), \
                 softmax(Q @ (Lamda[j:m](K[d[j]]).T + K_dquote.T) / sqrt(d_z)) @ (Lamda[j:m](V[d[j]]) + V_dquote))



@prove
def prove(Eq):
    from axiom import algebra, keras

    n, k, m = Symbol(integer=True, positive=True)
    r = Symbol(shape=(n,), integer=True)
    d_z = Symbol(integer=True, positive=True)
    Q = Symbol(shape=(n, d_z), real=True)
    K = Symbol(shape=(n, d_z), real=True)
    V = Symbol(shape=(n, d_z), real=True)
    d = Symbol(shape=(oo,), integer=True)
    i, j = Symbol(integer=True)
    w_K = Symbol("w^K", shape=(2 * k + 1, d_z), real=True)
    w_V = Symbol("w^V", shape=(2 * k + 1, d_z), real=True)
    K_quote = Symbol(shape=(n, n, d_z), real=True)
    V_quote = Symbol(shape=(n, n, d_z), real=True)
    K_dquote = Symbol('K^\"', real=True, shape=(n, m, d_z))
    V_dquote = Symbol('V^\"', real=True, shape=(n, m, d_z))
    s = d[:m].cup_finiteset(j)
    Eq << apply(
        Equal(Card(s), m),
        Subset(s, Range(n)),
        Equal(K_quote, Lamda[j:n, i:n](w_K[k + clip(r[j] - r[i], -k, k)])),
        Equal(V_quote, Lamda[j:n, i:n](w_V[k + clip(r[j] - r[i], -k, k)])),
        Equal(K_dquote, Lamda[j:m, i:n](w_K[k + clip(r[d[j]] - r[i], -k, k)])),
        Equal(V_dquote, Lamda[j:m, i:n](w_V[k + clip(r[d[j]] - r[i], -k, k)])),
        Q, K, V)

    Eq <<= Eq[2][:, d[j]], Eq[3][:, d[j]]

    Eq <<= algebra.eq.imply.eq.lamda.apply(Eq[-2], (j, 0, m)), algebra.eq.imply.eq.lamda.apply(Eq[-1], (j, 0, m))

    Eq <<= algebra.eq.imply.eq.transpose.apply(Eq[-2], 1), algebra.eq.imply.eq.transpose.apply(Eq[-1], 1)

    Eq <<= algebra.eq.eq.imply.eq.transit.apply(Eq[-2], Eq[4]), algebra.eq.eq.imply.eq.transit.apply(Eq[-1], Eq[5])

    Eq << keras.eq_card.subset_cup.imply.eq.matmul.softmax.position_representation.relative.gather.apply(Eq[0], Eq[1], Q, K, V, K_quote, V_quote)

    Eq << Eq[-1].subs(Eq[-3], Eq[-2])

    


if __name__ == '__main__':
    run()
# created on 2022-01-11
