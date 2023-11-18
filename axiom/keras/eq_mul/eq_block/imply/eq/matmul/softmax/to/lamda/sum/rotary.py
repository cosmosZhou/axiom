from util import *


from axiom.keras.eq_mul.imply.eq.matmul.position_representation import rotary_matrix, extract

@apply
def apply(eq_theta, eq_R, Q, K, V, j):
    Rk, d, alpha, θ, b, k, i, *_ = extract(eq_theta, eq_R)
    n = Q.shape[0]
    Ri = Rk.subs(k, i)
    return Equal(
        Softmax((Lamda[i:n](Ri @ Q[i]) @ Lamda[i:n](Ri @ K[i]).T) / sqrt(d)) @ V,
        Lamda[j:d, i:n](Sum[k:n](V[k, j] * Exp((S[K[k, :d / 2] * Q[i, :d / 2] + K[k, d / 2:] * Q[i, d / 2:], (K[k, :d / 2] * Q[i, d / 2:] - Q[i, :d / 2] * K[k, d / 2:])] @ [cos(θ[k - i]), sin(θ[k - i])]) / sqrt(d))) / ReducedSum(Exp((Q[i] @ Ri.T @ Lamda[i:n](Ri @ K[i]).T) / sqrt(d)))))

@prove
def prove(Eq):
    from axiom import keras, algebra, discrete

    # n denotes sequence length (seq_length)
    # b denotes 10000
    n, b = Symbol(integer=True, positive=True)
    # d denotes embedding size which must be even
    d = Symbol(integer=True, positive=True, even=True)
    # R denotes rotary matrix
    R = Function(shape=(d, d), real=True)
    θ = Symbol(shape=(n, d / 2), real=True)
    # k, t denote token index
    # i denotes row index
    i, j, k, t = Symbol(integer=True)
    Q, K, V = Symbol(shape=(n, d), real=True)
    # λ denotes scaling factor
    λ = Symbol(real=True)
    Eq << apply(*rotary_matrix(R, θ, d, b, k, i, λ), Q, K, V, j)

    Eq << Eq[-1].lhs.this.apply(keras.matmul.softmax.to.lamda.sum.scaled_dot_product_attention, i, j, k)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.limits.domain_defined, simplify=None)

    Eq << keras.eq_mul.eq_block.imply.eq.matmul.position_representation.rotary.apply(*Eq[:2], i)

    Eq.final = Eq[-2].subs(Eq[-1])

    Eq << keras.eq_mul.eq_block.imply.eq.matmul.to.add.position_representation.rotary.apply(*Eq[:2], K[i])

    Eq << Eq[-1].subs(k, k - t).subs(i, k).subs(t, i)

    Eq << discrete.eq.imply.eq.rmatmul.apply(Eq[-1], Q[i])

    Eq << Eq[-1].subs(Eq[0].subs(k, k - i))

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.sum)

    Eq << Eq[-1].this.find(Sum[2]).apply(algebra.sum.limits.subs.offset, d / 2)

    Eq << Eq[-1].this.rhs.apply(algebra.add.to.sum)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.rhs.expr.args[1:3].apply(algebra.add.to.mul)

    Eq.matmul_QRK = Eq[-1].this.rhs.expr.args[1:].apply(algebra.add.to.mul)

    Eq << Eq[2].find(BlockMatrix @ BlockMatrix).this.apply(discrete.matmul.to.block)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(discrete.matmul.to.sum)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(discrete.matmul.to.sum)

    Eq << Eq[-1].subs(Eq[0].subs(k, k - i)[j])

    Eq << Eq[-1].this.rhs.apply(algebra.add.to.sum)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-1], Eq.matmul_QRK)

    Eq << Eq.final.subs(Eq[-1].reversed)





if __name__ == '__main__':
    run()
# created on 2023-06-09
# updated on 2023-09-16
