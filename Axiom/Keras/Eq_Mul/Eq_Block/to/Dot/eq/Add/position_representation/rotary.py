from util import *

@apply
def apply(eq_theta, eq_R, xt):
    from Axiom.Keras.Eq_Mul.to.Eq.Dot.position_representation import extract
    Rk, d, alpha, θ, b, k, *_ = extract(eq_theta, eq_R)
    return Equal(
        Rk @ xt,
        xt * Cos(alpha) + BlockMatrix(-xt[d / 2:], xt[:d / 2]) * Sin(alpha))

@prove
def prove(Eq):
    from Axiom import Algebra, Discrete, Geometry
    from Axiom.Keras.Eq_Mul.to.Eq.Dot.position_representation import rotary_matrix
    # n denotes sequence length (seq_length)
    # b denotes 10000
    n, b = Symbol(integer=True, positive=True)
    # d denotes embedding size which must be even
    d = Symbol(integer=True, positive=True, even=True)
    # x_k denotes token embedding at index k (ie, x denotes sentence embedding)
    x = Symbol(shape=(n, d), real=True)
    # R denotes rotary matrix function
    R = Function(shape=(d, d), real=True)
    θ = Symbol(shape=(n, d / 2), real=True)
    # k denotes token index
    # i denotes row index
    i, k, t = Symbol(integer=True)
    # λ denotes scaling factor
    λ = Symbol(real=True)
    Eq << apply(*rotary_matrix(R, θ, d, b, k, i, λ), x[t])

    Eq << Eq[1] @ x[t]

    Eq << Eq[-1].this.rhs.args[1].apply(Algebra.Expr.eq.Block, d / 2)

    Eq << Eq[-1].this.rhs.apply(Discrete.Dot.eq.Block, deep=True)

    Eq << Eq[-1].subs(Eq[0])

    Eq <<= Eq[-1].rhs.find(MatMul).this.apply(Discrete.Dot.eq.Lamda), \
        Eq[-1].rhs.find(-~MatMul).this.apply(Discrete.Dot.eq.Lamda), \
        Eq[-1].rhs.args[1].find(MatMul).this.apply(Discrete.Dot.eq.Lamda), \
        Eq[-1].rhs.find(MatMul + ~MatMul).this.apply(Discrete.Dot.eq.Lamda)

    Eq << Eq[-5].subs(*Eq[-4:])

    Eq << Eq[-1].this.rhs.apply(Algebra.Block.eq.Add.Block, (-1, slice(1, None)))

    Eq << Eq[-1].this.find(BlockMatrix).apply(Algebra.Block.eq.Mul.Block)

    Eq << Eq[-1].this.find(BlockMatrix).apply(Algebra.Block.eq.Mul.Block)

    Eq <<= Eq[-1].find(Lamda).this.apply(Geometry.Lamda.eq.Cos), Eq[-1].find(Lamda[Sin]).this.apply(Geometry.Lamda.eq.Sin)

    Eq << Eq[-1].rhs.find(Lamda).this.apply(Algebra.Lamda.eq.Pow)

    Eq << Eq[-4].subs(*Eq[-3:])

    Eq << Eq[-1].this.find(BlockMatrix).apply(Geometry.Block.eq.Cos)

    Eq << Eq[-1].this.find(BlockMatrix * ~BlockMatrix).apply(Geometry.Block.eq.Sin)

    Eq << Eq[-1].subs(Eq[0].reversed)

    # reference:
    # https://nn.labml.ai/transformers/rope/index.html
    # https://openaccess.thecvf.com/content/WACV2022/papers/Jeevan_Resource-Efficient_Hybrid_X-Formers_for_Vision_WACV_2022_paper.pdf




if __name__ == '__main__':
    run()
# created on 2023-06-06
# updated on 2023-09-20
