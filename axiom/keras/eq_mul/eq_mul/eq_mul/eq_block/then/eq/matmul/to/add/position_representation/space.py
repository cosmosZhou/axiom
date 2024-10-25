from util import *

from axiom.keras.eq_mul.eq_mul.eq_mul.eq_block.then.eq.matmul.position_representation.space import rotary_matrix, extract

@apply
def apply(eq_theta_r, eq_theta_c, eq_theta_z, eq_R, xt, r, c, z):
    d_r, d_c, d_z, θ_r, θ_c, θ_z, Rijk, i, j, k, h = extract(eq_theta_r, eq_theta_c, eq_theta_z, eq_R)
    alpha = [θ_r[r[h]], θ_c[c[h]], θ_z[z[h]], θ_r[r[h]], θ_c[c[h]], θ_z[z[h]]]
    d = d_r + d_c + d_z
    d /= 2
    return Equal(
        Rijk.subs(i, r[h]).subs(j, c[h]).subs(k, z[h]) @ xt,
        xt * cos(alpha) + [-xt[d:], xt[:d]] * sin(alpha))

@prove
def prove(Eq):
    from axiom import algebra, discrete, geometry

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
    # x_k denotes token embedding at index k (ie, x denotes sentence embedding)
    x = Symbol(shape=(n, d), real=True)
    # R denotes rotary matrix function
    R = Function(shape=(d, d), real=True)
    θ_r = Symbol(format_r % "θ", shape=(n, d_r / 2), real=True)
    θ_c = Symbol(format_c % "θ", shape=(n, d_c / 2), real=True)
    θ_z = Symbol(format_z % "θ", shape=(n, d_z / 2), real=True)
    # t denotes time step
    # i denotes row index, j denotes column index, k denotes column index
    i, j, t, k, h = Symbol(integer=True)
    # r, c, z denote the row index, column index, vertical index respectively, each token has a (r[t], c[t], z[t]) three-demensional index
    r, c, z = Symbol(integer=True, shape=(n,))
    # λ denotes scaling factor, default to 1
    λ_r = Symbol(format_r % "λ", real=True)
    λ_c = Symbol(format_c % "λ", real=True)
    λ_z = Symbol(format_z % "λ", real=True)
    Eq << apply(*rotary_matrix(d_r, d_c, d_z, b_r, b_c, b_z, λ_r, λ_c, λ_z, θ_r, θ_c, θ_z, R, i, j, k, h), x[t], r, c, z)

    Eq << Eq[3].subs(i, r[h]).subs(j, c[h]).subs(k, z[h]) @ x[t]

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.expr.to.block, (d_r + d_c + d_z) / 2)

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.block, deep=True)

    Eq << Eq[-1].this.rhs.apply(algebra.block.to.add.block, (-1, slice(1, None)))

    Eq <<= Eq[-1].rhs.find(MatMul).this.apply(discrete.matmul.identity.to.mul), \
        Eq[-1].find(MatMul[2]).this.apply(discrete.matmul.identity.to.mul), \
        Eq[-1].find(-~MatMul).this.apply(discrete.matmul.identity.to.mul), \
        Eq[-1].rhs.args[1].find(MatMul).this.apply(discrete.matmul.identity.to.mul)

    Eq << Eq[-5].subs(*Eq[-4:])

    Eq << Eq[-1].this.find(BlockMatrix).apply(algebra.block.to.mul.block)

    Eq << Eq[-1].this.find(BlockMatrix).apply(algebra.block.to.mul.block)

    Eq << Eq[-1].this.find(BlockMatrix).apply(geometry.block.to.cos)

    Eq << Eq[-1].this.find(BlockMatrix[2]).apply(geometry.block.to.sin)

    # reference:
    # https://nn.labml.ai/transformers/rope/index.html




if __name__ == '__main__':
    run()
# created on 2023-09-16
# updated on 2023-09-18
