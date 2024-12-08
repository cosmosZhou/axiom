from util import *


@apply
def apply(eq_R):
    ((R, t), (S[R], k)), R[k - t] = eq_R.of(Equal[Transpose[Indexed] @ Indexed])
    return Equal(eq_R.lhs, Piecewise((R[k - t], k >= t), (R[t - k].T, True)))

@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    # n denotes sequence length (seq_length)
    n = Symbol(integer=True, positive=True)
    # d denotes embedding size which must be even
    d = Symbol(integer=True, positive=True, even=True)
    # R denotes rotary matrix
    R = Symbol(shape=(n, d, d), real=True)
    # k, t denote token index
    j, k, t = Symbol(integer=True)
    Eq << apply(Equal(R[t].T @ R[k], R[k - t]))


    Eq << Algebra.Cond.to.All.domain_defined.apply(Eq[0], k)

    Eq << Algebra.All.to.Imply.apply(Eq[-1])

    Eq << Eq[-1].this(t).find(Max).simplify()

    Eq << Eq[-1].this(t).find(Min).simplify()

    Eq << Eq[-1].this.lhs.apply(Sets.In_Range.of.And)

    Eq << Eq[-1].this(k).find(Less).simplify()

    Eq << Eq[-1].subs(k, j).subs(t, k).subs(j, t)

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.to.Eq.Transpose)

    Eq << Eq[-1].this.lhs.reversed

    Eq << Eq[-1].this.lhs.apply(Algebra.Le.of.Lt)

    Eq << Algebra.Cond_Piece.of.And.Imply.apply(Eq[1])



if __name__ == '__main__':
    run()
# created on 2023-09-16
