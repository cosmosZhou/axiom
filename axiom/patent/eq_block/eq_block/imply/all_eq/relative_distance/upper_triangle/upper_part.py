from util import *


@apply
def apply(eq_V, eq_V_quote):
    ((w, (k, (r_relative, S[-k], S[k]))), j_limit, i_limit), V = eq_V.of(Equal[Lamda[Indexed[Symbol, Add[clip]]]])

    j, S[0], n = j_limit
    i, S[0], S[n] = i_limit

    (r, S[j]), (S[r], S[i]) = r_relative.of(Indexed - Indexed)

    ((S[w], clip_index), (S[j], S[0], u), S[i_limit]), V_quote = eq_V_quote.of(Equal[Lamda[Indexed]])
    S[k], (((S[r], S[Min(j + i, n - 1)]), (S[r], S[i])), S[-k], S[k]) = clip_index.of(Add[clip[Indexed - Indexed]])

    assert n >= 2 and u >= 2 and u <= n

    return All[i:n - u](Equal(V[i, i:i + u], V_quote[i]))


@prove
def prove(Eq):
    from axiom import algebra

    n, k = Symbol(domain=Range(2, oo))
    u = Symbol(domain=Range(2, n + 1))
    V = Symbol(shape=(n, n), real=True)
    V_quote = Symbol(shape=(n, u), real=True)
    r = Symbol(shape=(n,), integer=True)
    w = Symbol(shape=(k * 2 + 1,), integer=True)
    i, j = Symbol(integer=True)
    Eq << apply(
        Equal(V, Lamda[j:n, i:n]((w[k + clip(r[j] - r[i], -k, k)]))),
        Equal(V_quote, Lamda[j:u, i:n](w[k + clip(r[Min(n - 1, i + j)] - r[i], -k, k)])))

    Eq <<= Eq[0][i]

    Eq <<= algebra.cond.imply.all.restrict.apply(Eq[-1], (i, 0, n - u), simplify=None)

    Eq << algebra.all_eq.imply.all_eq.slice.apply(Eq[-1], slice(i, i + u))

    Eq << Eq[-1].this.find(~Indexed -Indexed).args[1].apply(algebra.expr.to.piece, upper=n - 1)

    Eq.V_lower = Eq[-1].this(i).expr.rhs(j).find(GreaterEqual).simplify()

    Eq << Eq[1][i]

    Eq << algebra.cond.imply.all.restrict.apply(Eq[-1], (i, 0, n - u), simplify=None)

    

    

    Eq <<= Eq.V_lower & Eq[-1]

    Eq << Eq[-1].this.expr.apply(algebra.eq.eq.imply.eq.transit)

    


if __name__ == '__main__':
    run()
# created on 2022-03-30
