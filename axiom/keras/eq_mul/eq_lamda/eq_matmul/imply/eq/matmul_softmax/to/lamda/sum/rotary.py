from util import *


from axiom.keras.eq_lamda.imply.eq.matmul.to.lamda.position_representation.rotary import rotary_matrix, extract

@apply
def apply(eq_theta, eq_R, eq_T, V):
    (R, n, d), b, (i, j, k) = extract(eq_R)
    (S[k], (S[b], ((S[i], (S[i], S[0], S[d / 2])), S[d]))), (θ, S[k]) = eq_theta.of(Equal[Symbol * Symbol ** (-2 * Lamda / Symbol), Indexed])

    ((((((K, j), (S[1], S[d], S[2])), ((Q, S[i]), (S[1], S[d], S[2]))), S[K[j, ::2] * Q[i, ::2]]), S[θ[j - i]]), (S[K[j, ::2] * Q[i, 1::2] - K[j, 1::2] * Q[i, ::2]], S[θ[j - i]])), (T, S[i], S[j]) = \
    eq_T.of(Equal[(Sliced[Indexed] * Sliced[Indexed] + Expr) @ Cos + Expr @ Sin, Indexed])
    return Equal(
        Softmax((Lamda[i:n](R[i] @ Q[i]) @ Lamda[i:n](R[i] @ K[i]).T) / sqrt(d)) @ V,
        Lamda[j:d, i:n](Sum[k](V[k, j] * Exp(T[i, k] / sqrt(d))) / ReducedSum(Exp((Q[i] @ R[i].T @ Lamda[i:n](R[i] @ K[i]).T) / sqrt(d)))))

@prove
def prove(Eq):
    from axiom import keras, algebra, discrete, geometry

    #n denotes sequence length (seq_length)
    #b denotes 10000
    n, b = Symbol(integer=True, positive=True)
    #d denotes embedding size which must be even
    d = Symbol(integer=True, positive=True, even=True)
    #i denotes token index
    #j denotes row index
    #k denotes column index
    i, j, k = Symbol(integer=True)
    Q, K, V = Symbol(shape=(n, d), real=True)
    #R denotes rotary matrix
    R = Symbol(shape=(n, d, d), real=True)
    T = Symbol(shape=(n, n), real=True)
    θ = Symbol(shape=(n, d / 2), real=True)
    Eq << apply(
        Equal(θ[k], k / b ** (Lamda[i:d / 2](i) * 2 / d)),
        Equal(R, rotary_matrix(n, d, b, i, j, k)),
        Equal(T[i, j], (K[j, ::2] * Q[i, ::2] + K[j, 1::2] * Q[i, 1::2]) @ cos(θ[j - i]) + (K[j, ::2] * Q[i, 1::2] - Q[i, ::2] * K[j, 1::2]) @ sin(θ[j - i])),
        V)

    Eq << Eq[-1].lhs.this.apply(keras.matmul_softmax.to.lamda.sum.scaled_dot_product_attention, i, j, k)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.limits.domain_defined, simplify=None)

    Eq << keras.eq_lamda.imply.eq.matmul.to.piece.position_representation.rotary.apply(Eq[1]).subs(j, k)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.rhs().find(Max).simplify()

    Eq.final = Eq[-1].this.rhs().find(Min).simplify()

    Eq <<= keras.eq_lamda.imply.eq.matmul.to.lamda.position_representation.rotary.apply(Eq[1], K[k]), \
        keras.eq_lamda.imply.eq.matmul_transpose.to.lamda.position_representation.rotary.apply(Eq[1], K[k])

    Eq <<= Eq[-2].subs(i, k - i), Eq[-1].subs(i, i - k)

    Eq <<= discrete.eq.imply.eq.rmatmul.apply(Eq[-2], Q[i]), discrete.eq.imply.eq.rmatmul.apply(Eq[-1], Q[i])

    Eq <<= Eq[-2].this.rhs.apply(discrete.matmul.to.sum), Eq[-1].this.rhs.apply(discrete.matmul.to.sum)

    Eq <<= Eq[-2].this.find(Sum).apply(algebra.sum.halve), Eq[-1].this.find(Sum).apply(algebra.sum.halve)

    Eq <<= Eq[-2].this.find(Sum).apply(algebra.sum.halve), Eq[-1].this.find(Sum).apply(algebra.sum.halve)

    Eq <<= Eq[-2].this.rhs.apply(algebra.add.to.sum), Eq[-1].this.rhs.apply(algebra.add.to.sum)

    Eq <<= Eq[-2].this.find(Mul[Add]).apply(algebra.mul.to.add), Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq <<= Eq[-2].this.find(Mul[Add]).apply(algebra.mul.to.add), Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq <<= Eq[-2].this.rhs.expr.args[1:3].apply(algebra.add.to.mul), Eq[-1].this.rhs.expr.args[1:3].apply(algebra.add.to.mul)

    Eq.matmul_QRK, Eq.matmul_QRTK = Eq[-2].this.rhs.expr.args[1:].apply(algebra.add.to.mul), Eq[-1].this.rhs.expr.args[1:].apply(algebra.add.to.mul)

    Eq << Eq[2].subs(j, k)

    Eq << Eq[-1].this.find(MatMul).apply(discrete.matmul.to.sum)

    Eq << Eq[-1].this.find(MatMul).apply(discrete.matmul.to.sum)

    Eq << Eq[-1].subs(Eq[0].subs(k, k - i)[j])

    Eq.T_def = Eq[-1].this.rhs.apply(algebra.add.to.sum)

    Eq <<= algebra.eq.eq.imply.eq.transit.apply(Eq.T_def, Eq.matmul_QRK)

    Eq <<= Eq.matmul_QRTK.this.find(Cos).apply(geometry.cos.neg)

    Eq <<= Eq[-1].this.find(Sin).apply(geometry.sin.to.neg.sin)

    Eq <<= algebra.eq.eq.imply.eq.transit.apply(Eq.T_def, Eq[-1])


    Eq << Eq.final.subs(Eq[-1].reversed, Eq[-4].reversed)
    Eq << Eq[-1].this.rhs().find(Min).simplify()
    Eq << Eq[-1].this.rhs().find(Max).simplify()
    Eq << Eq[-1].this.rhs().find(Union).simplify()
    Eq << Eq[3].this.rhs.simplify()




if __name__ == '__main__':
    run()
# created on 2023-05-30
# updated on 2023-06-16
