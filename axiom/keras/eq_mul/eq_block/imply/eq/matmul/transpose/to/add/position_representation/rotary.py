from util import *


from axiom.keras.eq_mul.eq_block.imply.eq.matmul.to.add.position_representation.rotary import rotary_matrix, extract
@apply
def apply(eq_theta, eq_R, x):
    Rk, d, alpha, θ, b, k, *_ = extract(eq_theta, eq_R)
    return Equal(
        Rk.T @ x, 
        x * Cos(alpha) + BlockMatrix(x[d / 2:], -x[:d / 2]) * Sin(alpha))

@prove
def prove(Eq):
    from axiom import algebra, discrete, geometry

    #n denotes sequence length (seq_length)
    #b denotes 10000
    n, b = Symbol(integer=True, positive=True)
    #d denotes embedding size which must be even
    d = Symbol(integer=True, positive=True, even=True)
    #x_k denotes token embedding at index k (ie, x denotes sentence embedding)
    x = Symbol(shape=(n, d), real=True)
    #R denotes rotary matrix function
    R = Function(shape=(d, d), real=True)
    θ = Symbol(shape=(n, d / 2), real=True)
    #k denote token index
    #i denotes row index
    i, k = Symbol(integer=True)
    #λ denotes scaling factor
    λ = Symbol(real=True)
    Eq << apply(*rotary_matrix(R, θ, d, b, k, i, λ), x[k])

    Eq << Eq[1].T @ x[k]

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.expr.to.block, d / 2)

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.block, deep=True)

    Eq << Eq[-1].subs(Eq[0])

    Eq <<= Eq[-1].rhs.find(MatMul).this.apply(discrete.matmul.to.lamda), \
        Eq[-1].rhs.find(-~MatMul).this.apply(discrete.matmul.to.lamda), \
        Eq[-1].rhs.args[1].find(MatMul).this.apply(discrete.matmul.to.lamda), \
        Eq[-1].rhs.find(MatMul + ~MatMul).this.apply(discrete.matmul.to.lamda)

    Eq << Eq[-5].subs(*Eq[-4:])

    Eq << Eq[-1].this.rhs.apply(algebra.block.to.add.block)

    Eq << Eq[-1].this.find(BlockMatrix).apply(algebra.block.to.mul.block)

    Eq << Eq[-1].this.find(BlockMatrix).apply(algebra.block.to.mul.block)

    Eq <<= Eq[-1].find(Lamda).this.apply(geometry.lamda.to.cos), Eq[-1].find(Lamda[Sin]).this.apply(geometry.lamda.to.sin)

    Eq << Eq[-1].rhs.find(Lamda).this.apply(algebra.lamda.to.pow)

    Eq << Eq[-4].subs(*Eq[-3:])

    Eq << Eq[-1].this.find(BlockMatrix).apply(geometry.block.to.cos)

    Eq << Eq[-1].this.find(BlockMatrix * ~BlockMatrix).apply(geometry.block.to.sin)

    Eq << Eq[-1].subs(Eq[0].reversed)

    
    


if __name__ == '__main__':
    run()
# created on 2023-06-09
# updated on 2023-09-16
