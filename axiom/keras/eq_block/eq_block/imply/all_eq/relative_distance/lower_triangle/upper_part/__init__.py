from util import *


@apply
def apply(eq_V, eq_V_quote):
    ((w, (k, (r_relative, S[-k], S[k]))), j_limit, i_limit), V = eq_V.of(Equal[Lamda[Indexed[Symbol, Add[clip]]]])

    j, S[0], n = j_limit
    i, S[0], S[n] = i_limit

    (r, S[j]), (S[r], S[i]) = r_relative.of(Indexed - Indexed)

    ((S[w], clip_index), (S[j], S[0], l), S[i_limit]), V_quote = eq_V_quote.of(Equal[Lamda[Indexed]])
    S[k], (((S[r], S[Min(j + relu(i - l + 1), n - 1)]), (S[r], S[i])), S[-k], S[k]) = clip_index.of(Add[clip[Indexed - Indexed]])

    assert n >= 2 and l >= 2 and l <= n

    return All[i:l](Equal(V[i, :i + 1], V_quote[i, :i + 1]))


@prove
def prove(Eq):
    from axiom import algebra, keras

    n, k = Symbol(domain=Range(2, oo))
    l = Symbol(domain=Range(2, n + 1))
    A = Symbol(shape=(n, n), real=True)
    V = Symbol(shape=(n, n), real=True)
    z, V_quote = Symbol(shape=(n, l), real=True)
    r = Symbol(shape=(n,), integer=True)
    w = Symbol(shape=(k * 2 + 1,), integer=True)
    i, j = Symbol(integer=True)
    Eq << apply(
        Equal(V, Lamda[j:n, i:n]((w[k + clip(r[j] - r[i], -k, k)]))),
        Equal(V_quote, Lamda[j:l, i:n](w[k + clip(r[Min(n - 1, relu(i - l + 1) + j)] - r[i], -k, k)])))

    Eq <<= Eq[0][i]

    Eq <<= algebra.cond.imply.all.restrict.apply(Eq[-1], (i, 0, l), simplify=None)

    Eq << algebra.all_eq.imply.all_eq.slice.apply(Eq[-1], slice(0, i + 1))

    Eq << Eq[-1].this.find(-Indexed + ~Indexed).args[1].apply(algebra.expr.to.piece, upper=n - 1)

    Eq.V_upper = Eq[-1].this(i).expr.rhs(j).find(GreaterEqual).simplify()

    Eq << Eq[1][i]

    Eq << algebra.cond.imply.all.restrict.apply(Eq[-1], (i, 0, l), simplify=None)

    Eq << algebra.all_eq.imply.all_eq.slice.apply(Eq[-1], slice(0, i + 1))

    Eq << Eq[-1].this.find(relu).apply(keras.relu.to.add.min)

    Eq << Eq[-1].this(i).find(-~Min).simplify()

    Eq <<= Eq.V_upper & Eq[-1]

    Eq << Eq[-1].this.expr.apply(algebra.eq.eq.imply.eq.transit)




if __name__ == '__main__':
    run()
# created on 2022-03-17
# updated on 2022-03-30
from . import tf
