from util import *


@apply
def apply(eq_A, eq_P, eq_P_quote, eq_I_quote, eq_I_dquote):
    ((I, k), limit), A = eq_A.of(Equal[Lamda[Bool[Indexed > 0]]])
    assert I >= 0
    S[k], S[0], n = limit
    ((S[k], S[limit]), S[A]), P = eq_P.of(Equal[Lamda + ReducedArgMax + 1])
    (S[P], (S[P[k]], S[limit])), P_quote = eq_P_quote.of(Equal[Symbol * Lamda[Bool[Expr < n + 1]]])
    (S[0], S[I]), I_quote = eq_I_quote.of(Equal[BlockMatrix])
    (S[I_quote[P_quote[k]]], S[limit]), I_dquote = eq_I_dquote.of(Equal[Lamda])

    return Equal(ReducedSum(I_dquote), ReducedSum(I))


@prove
def prove(Eq):
    from Axiom import Algebra, Keras

    k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True) # seq_length
    A = Symbol(integer=True, shape=(n,)) # attention_mask = (input_ids > 0).int()
    P = Symbol(integer=True, shape=(n,))
    # position_ids = torch.arange(1, seq_length + 1)[None, ].to(attention_mask.device)
    # position_ids += attention_mask.argmax(-1, keepdim=True)
    P_quote = Symbol(integer=True, shape=(n,))
    # position_ids *= (position_ids < seq_length + 1).int()
    I = Symbol(integer=True, nonnegative=True, shape=(n,)) # input_ids
    I_quote = Symbol(integer=True, shape=(n + 1,)) # input_ids = hstack(input_ids, 1)
    I_dquote = Symbol('I^"', integer=True, shape=(n,)) # input_ids = torch.gather(input_ids, 1, position_ids)
    Eq << apply(
        Equal(A, Lamda[k:n](Bool(I[k] > 0))),
        Equal(P, Lamda[k:n](k) + 1 + ReducedArgMax(A)),
        Equal(P_quote, P * Lamda[k:n](Bool(P[k] < n + 1))),
        Equal(I_quote, BlockMatrix(0, I)),
        Equal(I_dquote, Lamda[k:n](I_quote[P_quote[k]])))

    Eq << Eq[-1].this.lhs.apply(Algebra.ReducedSum.eq.Sum, k)

    Eq << Eq[-1].this.rhs.apply(Algebra.ReducedSum.eq.Sum, k)

    Eq << Eq[-1].subs(Eq[4], simplify=None)

    Eq << Eq[-1].subs(Eq[3], simplify=None)

    Eq << Eq[-1].subs(Eq[2], simplify=None)

    Eq << Eq[-1].subs(Eq[1], simplify=None)

    Eq << Eq[-1].this.find(Add < Add).apply(Algebra.Lt.simp.common_terms, simplify=None)

    Eq << Eq[-1].this.find(Add < Add).apply(Algebra.Lt.simp.common_terms, simplify=None)

    Eq << Eq[-1].this.find(Piecewise).apply(Algebra.Piece.swap, simplify=None)

    Eq << Eq[-1].this.find(GreaterEqual).apply(Algebra.Ge.equ.Gt.relax, simplify=None)

    Eq << Eq[-1].this.lhs().find(Greater).apply(Algebra.Gt_0.st.Mul, simplify=None)

    Eq << Eq[-1].this.find(Greater).apply(Algebra.Gt_0.equ.Cond)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.limits.subs.offset, -Eq[-1].find(ReducedArgMax))

    Eq << Eq[-1].this.lhs().find(Bool).simplify()

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.Add.split, cond=k < Eq[-1].find(ReducedArgMax))

    Eq << Keras.Eq_Lamda.to.Eq_0.Sum.padding_Left.apply(Eq[0])




if __name__ == '__main__':
    run()
# created on 2023-11-05