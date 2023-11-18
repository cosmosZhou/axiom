from util import *


@apply
def apply(eq_R):
    ((R, t), (S[R], k)), R[k - t] = eq_R.of(Equal[Transpose[Indexed] @ Indexed])
    return Equal(eq_R.lhs, Piecewise((R[k - t], k >= t), (R[t - k].T, True)))

@prove
def prove(Eq):
    from axiom import algebra, sets

    #n denotes sequence length (seq_length)
    #b denotes 10000
    n, b = Symbol(integer=True, positive=True)
    #d denotes embedding size which must be even
    d = Symbol(integer=True, positive=True, even=True)
    #R denotes rotary matrix
    R = Symbol(shape=(n, d, d), real=True)
    #k, t denote token index
    #i denotes row index
    i, j, k, t = Symbol(integer=True)
    Eq << apply(Equal(R[t].T @ R[k], R[k - t]))

    
    Eq << algebra.cond.imply.all.domain_defined.apply(Eq[0], k)
    Eq << algebra.all.imply.infer.apply(Eq[-1])
    Eq << Eq[-1].this(t).find(Max).simplify()
    Eq << Eq[-1].this(t).find(Min).simplify()
    Eq << Eq[-1].this.lhs.apply(sets.el_range.given.et)
    Eq << Eq[-1].this(k).find(Less).simplify()
    Eq << Eq[-1].subs(k, j).subs(t, k).subs(j, t)
    Eq << Eq[-1].this.rhs.apply(algebra.eq.imply.eq.transpose)
    Eq << Eq[-1].this.lhs.reversed
    Eq << Eq[-1].this.lhs.apply(algebra.le.given.lt)
    Eq << algebra.cond_piece.given.et.infer.apply(Eq[1])
    


if __name__ == '__main__':
    run()
# created on 2023-09-16
