from util import *


@apply
def apply(eq_theta, eq_R):
    from axiom.keras.eq_mul.eq_block.then.eq.matmul.to.add.position_representation.rotary import  extract
    Rk, d, alpha, θ, b, k, i, *_ = extract(eq_theta, eq_R)
    Ri = Rk.subs(k, i)
    return Equal(Ri.T, Ri ^ -1)

@prove
def prove(Eq):
    from axiom.keras.eq_mul.eq_block.then.eq.matmul.to.add.position_representation.rotary import rotary_matrix
    from axiom import keras, algebra, discrete

    # n denotes sequence length (seq_length)
    # b denotes 10000
    n, b = Symbol(integer=True, positive=True)
    # d denotes embedding size which must be even
    d = Symbol(integer=True, positive=True, even=True)
    # R denotes rotary matrix function
    R = Function(shape=(d, d), real=True)
    θ = Symbol(shape=(n, d / 2), real=True)
    # k, t denote token index
    # i denotes row index
    i, k, t = Symbol(integer=True)
    # λ denotes scaling factor
    λ = Symbol(real=True)
    Eq << apply(*rotary_matrix(R, θ, d, b, k, i, λ))

    Eq << keras.eq_mul.eq_block.then.eq.matmul.position_representation.rotary.apply(*Eq[:2], t)

    Eq << Eq[-1].subs(t, i).subs(k, i)

    Eq << Eq[1].subs(k, 0).subs(Eq[0].subs(k, 0))

    Eq << Eq[-1].this.rhs.apply(algebra.block.to.identity)

    Eq << Eq[-3].subs(Eq[-1])

    Eq << discrete.eq_matmul.then.eq.inverse.apply(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2023-06-16
# updated on 2023-09-16
