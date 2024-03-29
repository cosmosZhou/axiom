from util import *


from axiom.keras.eq_mul.eq_mul.eq_mul.eq_block.imply.eq.matmul.position_representation.space import rotary_matrix, extract

@apply
def apply(eq_theta_r, eq_theta_c, eq_theta_z, eq_R, Q, K, V, r, c, z, t):
    d_r, d_c, d_z, θ_r, θ_c, θ_z, Rijk, i, j, k, h = extract(eq_theta_r, eq_theta_c, eq_theta_z, eq_R)
    n = Q.shape[0]
    Rt = Rijk.subs(i, r[t]).subs(j, c[t]).subs(k, z[t])
    d = d_r + d_c + d_z
    θ = [θ_r[r[t] - r[i]], θ_c[c[t] - c[i]], θ_z[z[t] - z[i]]]
    return Equal(
        Softmax((Lamda[t:n](Rt @ Q[t]) @ Lamda[t:n](Rt @ K[t]).T) / sqrt(d)) @ V,
        Lamda[j:d, i:n](Sum[t](V[t, j] * Exp(S[K[t, :d / 2] * Q[i, :d / 2] + K[t, d / 2:] * Q[i, d / 2:], K[t, :d / 2] * Q[i, d / 2:] - K[t, d / 2:] * Q[i, :d / 2]] @ [cos(θ), sin(θ)] / sqrt(d))) / ReducedSum(Exp((Q[i] @ Rt.subs(t, i).T @ Lamda[i:n](Rt.subs(t, i) @ K[i]).T) / sqrt(d)))))

@prove(slow=True)
def prove(Eq):
    from axiom import keras, discrete, algebra, geometry

    # n denotes sequence length (seq_length)
    # b_r, b_c denotes 10000
    n = Symbol(integer=True, positive=True)
    format_supscript = r"^{\color{magenta} %s}"
    format_r = '%s' + format_supscript % 'r'
    format_c = '%s' + format_supscript % 'c'
    format_z = '%s' + format_supscript % 'z'
    b_r = Symbol(format_r.replace('^', '_') % 'b', integer=True, positive=True)
    b_c = Symbol(format_c.replace('^', '_') % 'b', integer=True, positive=True)
    b_z = Symbol(format_z.replace('^', '_') % 'b', integer=True, positive=True)
    # d, d_r, d_c, d_z denotes embedding size which must be divisible by 2, under the condition that d = d_r + d_c + d_z
    d_r = Symbol(format_r % 'd', integer=True, positive=True, even=True)
    d_c = Symbol(format_c % 'd', integer=True, positive=True, even=True)
    d_z = Symbol(format_z % 'd', integer=True, positive=True, even=True)
    d = d_r + d_c + d_z
    # R denotes rotary matrix function
    R = Function(shape=(d, d), real=True)
    θ_r = Symbol(format_r % "θ", shape=(n, d_r / 2), real=True)
    θ_c = Symbol(format_c % "θ", shape=(n, d_c / 2), real=True)
    θ_z = Symbol(format_z % "θ", shape=(n, d_z / 2), real=True)
    # t denotes time step
    # i denotes row index, j denotes column index
    i, j, k, t, h = Symbol(integer=True)
    # r, c, z denote the row index and column index respectively, each token has a (r[t], c[t], z[t]) two-demensional index
    r, c, z = Symbol(integer=True, shape=(n,))
    # λ denotes scaling factor, default to 1
    λ_r = Symbol(format_r % "λ", real=True)
    λ_c = Symbol(format_c % "λ", real=True)
    λ_z = Symbol(format_z % "λ", real=True)
    Q, K, V = Symbol(shape=(n, d), real=True)
    Eq << apply(*rotary_matrix(d_r, d_c, d_z, b_r, b_c, b_z, λ_r, λ_c, λ_z, θ_r, θ_c, θ_z, R, i, j, k, h), Q, K, V, r, c, z, t)

    Eq << Eq[-1].lhs.this.apply(keras.matmul.softmax.to.lamda.sum.scaled_dot_product_attention, i, j, t)

    i_quote, j_quote, k_quote = Symbol(integer=True)
    Eq << keras.eq_mul.eq_mul.eq_mul.eq_block.imply.eq.matmul.position_representation.space.apply(*Eq[:4], i_quote, j_quote, k_quote)

    Eq << Eq[-1].subs(i, r[t]).subs(j, c[t]).subs(k, z[t]).subs(i_quote, r[i]).subs(j_quote, c[i]).subs(k_quote, z[i])

    Eq.final = Eq[-3].subs(Eq[-1])

    Eq << keras.eq_mul.eq_mul.eq_mul.eq_block.imply.eq.matmul.to.add.position_representation.space.apply(*Eq[:4], K[t], r, c, z)

    Eq << Eq[-1].subs(r[h], r[t] - r[i]).subs(c[h], c[t] - c[i]).subs(z[h], z[t] - z[i])

    Eq << discrete.eq.imply.eq.rmatmul.apply(Eq[-1], Q[i])

    Eq.theta_r, Eq.theta_c, Eq.theta_z = Eq[0].subs(i, r[t] - r[i]), Eq[1].subs(j, c[t] - c[i]), Eq[2].subs(k, z[t] - z[i])

    Eq << Eq[-1].subs(Eq.theta_r, Eq.theta_c, Eq.theta_z)

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.sum)

    Eq <<= Eq[-1].find(Sum).this.apply(algebra.sum.limits.subs.offset, d_r / 2), \
        Eq[-1].find(Sum[2]).this.apply(algebra.sum.limits.subs.offset, d_r + (d_c + d_z) / 2),\
        Eq[-1].find(Sum[4]).this.apply(algebra.sum.limits.subs.offset, (d_r + d_c + d_z) / 2),\
        Eq[-1].find(Sum[5]).this.apply(algebra.sum.limits.subs.offset, (d_r + d_c) / 2),\
        Eq[-1].find(Sum[6]).this.apply(algebra.sum.limits.subs.offset, d_r + d_c + d_z / 2)

    Eq << Eq[-6].subs(*Eq[-5:])

    Eq << Eq[-1].subs(Eq.theta_r[j].reversed, Eq.theta_c[j].reversed, Eq.theta_z[j].reversed)

    Eq <<= Add(*Eq[-1].rhs.args[::3]).this.apply(algebra.add.to.sum),\
        Add(*Eq[-1].rhs.args[1::3]).this.apply(algebra.add.to.sum),\
        Add(*Eq[-1].rhs.args[2::3]).this.apply(algebra.add.to.sum)

    Eq << Eq[-4].subs(*Eq[-3:])

    Eq <<= Eq[-1].find(Mul[Add]).this.apply(algebra.mul.to.add),\
        Eq[-1].find(Mul[2][Add]).this.apply(algebra.mul.to.add),\
        Eq[-1].find(Sum[2], Mul[Add]).this.apply(algebra.mul.to.add), \
        Eq[-1].find(Sum[2], Mul[Add][2]).this.apply(algebra.mul.to.add),\
        Eq[-1].find(Sum[3], Mul[Add]).this.apply(algebra.mul.to.add), \
        Eq[-1].find(Sum[3], Mul[Add][2]).this.apply(algebra.mul.to.add)

    Eq << Eq[-7].subs(*Eq[-6:])

    Eq <<= Add(*Eq[-1].find(Sum).expr.args[1:3]).this.apply(algebra.add.to.mul), \
        Add(*Eq[-1].find(Sum).expr.args[::3]).this.apply(algebra.add.to.mul), \
        Add(*Eq[-1].find(Sum[2]).expr.args[1:3]).this.apply(algebra.add.to.mul),\
        Add(*Eq[-1].find(Sum[2]).expr.args[::3]).this.apply(algebra.add.to.mul),\
        Add(*Eq[-1].find(Sum[3]).expr.args[1:3]).this.apply(algebra.add.to.mul),\
        Add(*Eq[-1].find(Sum[3]).expr.args[::3]).this.apply(algebra.add.to.mul)

    Eq << Eq[-7].subs(*Eq[-6:])

    Eq <<= Eq[-1].find(Sum).this.apply(discrete.sum.to.add.matmul),\
        Eq[-1].find(Sum[2]).this.apply(discrete.sum.to.add.matmul),\
        Eq[-1].find(Sum[3]).this.apply(discrete.sum.to.add.matmul)

    Eq << Eq[-4].subs(*Eq[-3:])

    Eq <<= Eq[-1].find(Lamda).this.apply(algebra.lamda.to.add),\
        Eq[-1].find(MatMul[2][~Lamda]).this.apply(algebra.lamda.to.add),\
        Eq[-1].find(MatMul[3][~Lamda]).this.apply(algebra.lamda.to.add),\
        Eq[-1].find(MatMul[4][~Lamda]).this.apply(algebra.lamda.to.add),\
        Eq[-1].find(MatMul[5][~Lamda]).this.apply(algebra.lamda.to.add),\
        Eq[-1].find(MatMul[6][~Lamda]).this.apply(algebra.lamda.to.add)

    Eq << Eq[-7].subs(*Eq[-6:])

    Eq <<= Add(*Eq[-1].rhs.args[:3]).this.apply(discrete.add.to.matmul.block, swap=(False, True)), Add(*Eq[-1].rhs.args[3:]).this.apply(discrete.add.to.matmul.block, swap=(False, True))

    Eq << Eq[-3].subs(*Eq[-2:])

    Eq << Eq[-1].this.find(BlockMatrix).apply(algebra.block.to.add.block, (-1, slice(-1, None), slice(-1, None)))

    Eq << Eq[-1].this.find(Add[~BlockMatrix]).apply(algebra.block.to.mul.block)

    Eq << Eq[-1].this.find(Add[~BlockMatrix]).apply(algebra.block.to.mul.block)

    Eq << Eq[-1].this.find((~BlockMatrix) @ BlockMatrix).apply(algebra.block.to.add.block, (-1, -1, -1))

    Eq << Eq[-1].this.find(Add[~BlockMatrix]).apply(algebra.block.to.mul.block)

    Eq << Eq[-1].this.find(Add[~BlockMatrix]).apply(algebra.block.to.mul.block)

    Eq << Eq[-1].this.find(Mul[~BlockMatrix]).apply(algebra.block.to.neg.block)

    Eq <<= Eq[-1].find(BlockMatrix[Cos]).this.apply(geometry.block.to.cos), Eq[-1].find(BlockMatrix[Sin]).this.apply(geometry.block.to.sin)

    Eq << Eq[-3].subs(*Eq[-2:])

    Eq << Eq[-1].this.rhs.apply(discrete.add.to.matmul.block, swap=True)

    Eq << Eq.final.subs(Eq[-1])

    


if __name__ == '__main__':
    run()
# created on 2023-09-20
