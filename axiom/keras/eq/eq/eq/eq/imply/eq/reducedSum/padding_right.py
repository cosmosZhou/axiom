from util import *


@apply
def apply(eq_A, eq_P, eq_P_quote, eq_I_quote):
    ((I, k), limit), A = eq_A.of(Equal[Lamda[Bool[Indexed > 0]]])
    assert I >= 0
    S[k], S[0], n = limit
    ((S[k], S[limit]), S[A]), P = eq_P.of(Equal[Lamda + ReducedArgMax])
    (S[P], (S[P[k]], S[limit])), P_quote = eq_P_quote.of(Equal[Symbol - n * Lamda[Bool[Expr >= n]]])
    (S[I[P_quote[k]]], S[limit]), I_quote = eq_I_quote.of(Equal[Lamda])

    return Equal(ReducedSum(I_quote), ReducedSum(I))


@prove
def prove(Eq):
    from axiom import algebra

    k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True) # seq_length
    A = Symbol(integer=True, shape=(n,)) # attention_mask = (input_ids > 0).int()
    P = Symbol(integer=True, shape=(n,))
    # position_ids = torch.arange(seq_length)[None, ].to(attention_mask.device)
    # position_ids += attention_mask.argmax(-1, keepdim=True)
    P_quote = Symbol(integer=True, shape=(n,))# position_ids -= (position_ids >= seq_length).int() * seq_length
    I = Symbol(integer=True, nonnegative=True, shape=(n,)) # input_ids
    I_quote = Symbol(integer=True, shape=(n,)) # input_ids = torch.gather(input_ids, 1, position_ids)
    Eq << apply(
        Equal(A, Lamda[k:n](Bool(I[k] > 0))),
        Equal(P, Lamda[k:n](k) + ReducedArgMax(A)),
        Equal(P_quote, P - n * Lamda[k:n](Bool(P[k] >= n))),
        Equal(I_quote, Lamda[k:n](I[P_quote[k]])))

    Eq << Eq[-1].this.lhs.apply(algebra.reducedSum.to.sum, k)

    Eq << Eq[-1].this.rhs.apply(algebra.reducedSum.to.sum, k)

    Eq << Eq[-1].subs(Eq[3], Eq[2], Eq[1])

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piece)

    Eq << Eq[-1].this.lhs.args[0].apply(algebra.sum.limits.subs.offset, -Eq[-1].find(ReducedArgMax))

    Eq << Eq[-1].this.lhs.args[1].apply(algebra.sum.limits.subs.offset, n -Eq[-1].find(ReducedArgMax), simplify=None)

    


if __name__ == '__main__':
    run()
# created on 2023-11-07
