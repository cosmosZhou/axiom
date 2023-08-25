from util import *


def rotary_matrix(R, θ, d, b, k, i):
    return Equal(θ[k], k / b ** (Lamda[i:d / 2](i) / d)), \
        Equal(R[k], BlockMatrix([
            [Identity(d / 2) * cos(θ[k]), -Identity(d / 2) * sin(θ[k])],
            [Identity(d / 2) * sin(θ[k]), Identity(d / 2) * cos(θ[k])]]))

def extract(eq_theta, eq_R):
    (k, (b, ((i, limit_i), d))), θ = eq_theta.of(Equal[Symbol / Symbol ** (Lamda / Symbol)])
    S[i], S[0], S[d / 2] = limit_i
    ((cos, sin), (S[-sin], S[cos])), R = eq_R.of(Equal[BlockMatrix[BlockMatrix[1], BlockMatrix[1]]])
    S[θ] = cos.of(Cos[Expr] * Identity)
    S[θ] = sin.of(-Identity * Sin[Expr])
    alpha = BlockMatrix(θ, θ)
    θ, S[k] = θ.of(Indexed)
    assert d.is_even
    R, S[k] = R.of(Indexed)
    return R, d, alpha, θ, b, k, i
    
@apply
def apply(eq_theta, eq_R, x):
    R, d, alpha, θ, b, k, i = extract(eq_theta, eq_R)
    return Equal(
        R[k] @ x, 
        x * Cos(alpha) + BlockMatrix(-x[d / 2:], x[:d / 2]) * Sin(alpha))

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
    #R denotes rotary matrix
    R = Symbol(shape=(n, d, d), real=True)
    θ = Symbol(shape=(n, d / 2), real=True)
    #k denotes token index
    #i denotes row index
    i, k = Symbol(integer=True)
    Eq << apply(*rotary_matrix(R, θ, d, b, k, i), x[k])

    Eq << Eq[1] @ x[k]

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.expr.to.block, d / 2)

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.block, deep=True)

    Eq << Eq[-1].subs(Eq[0])

    Eq <<= Eq[-1].rhs.find(MatMul).this.apply(discrete.matmul.to.lamda), \
        Eq[-1].rhs.find(-~MatMul).this.apply(discrete.matmul.to.lamda), \
        Eq[-1].rhs.args[1].find(MatMul).this.apply(discrete.matmul.to.lamda), \
        Eq[-1].rhs.find(MatMul + ~MatMul).this.apply(discrete.matmul.to.lamda)

    Eq << Eq[-5].subs(*Eq[-4:])

    Eq << Eq[-1].this.rhs.apply(algebra.block.to.add.block, (-1, slice(1, None)))

    Eq << Eq[-1].this.find(BlockMatrix).apply(algebra.block.to.mul.block)

    Eq << Eq[-1].this.find(BlockMatrix).apply(algebra.block.to.mul.block)

    Eq <<= Eq[-1].find(Lamda).this.apply(geometry.lamda.to.cos), Eq[-1].find(Lamda[Sin]).this.apply(geometry.lamda.to.sin)

    Eq << Eq[-1].rhs.find(Lamda).this.apply(algebra.lamda.to.pow)

    Eq << Eq[-4].subs(*Eq[-3:])

    Eq << Eq[-1].this.find(BlockMatrix).apply(geometry.block.to.cos)

    Eq << Eq[-1].this.find(BlockMatrix * ~BlockMatrix).apply(geometry.block.to.sin)

    Eq << Eq[-1].subs(Eq[0].reversed)

    #reference:
    #https://nn.labml.ai/transformers/rope/index.html
    
    


if __name__ == '__main__':
    run()
# created on 2023-06-06
# updated on 2023-06-16
