from util import *


from axiom.keras.eq_mul.eq_block.imply.eq.matmul.to.add.position_representation.rotary import rotary_matrix, extract
@apply
def apply(eq_theta, eq_R, t):
    R, d, alpha, θ, b, k, i = extract(eq_theta, eq_R)
    return Equal(R[t].T @ R[k], Piecewise((R[k - t], k >= t), (R[t - k].T, True)))

@prove
def prove(Eq):
    from axiom import discrete, algebra, geometry, sets

    #n denotes sequence length (seq_length)
    #b denotes 10000
    n, b = Symbol(integer=True, positive=True)
    #d denotes embedding size which must be even
    d = Symbol(integer=True, positive=True, even=True)
    #R denotes rotary matrix
    R = Symbol(shape=(n, d, d), real=True)
    θ = Symbol(shape=(n, d / 2), real=True)
    #k, t denote token index
    #i denotes row index
    i, k, t = Symbol(integer=True)
    Eq << apply(*rotary_matrix(R, θ, d, b, k, i), t)

    Eq << Eq[1].subs(Eq[0])

    Eq << Eq[-1].subs(k, t).T @ Eq[-1]

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.block, deep=True)

    Eq <<= Eq[-1].rhs.find(MatMul).this.apply(discrete.matmul.to.lamda),\
        Eq[-1].rhs.find(MatMul[2]).this.apply(discrete.matmul.to.lamda),\
        Eq[-1].rhs.find((~MatMul) - MatMul).this.apply(discrete.matmul.to.lamda),\
        Eq[-1].rhs.find(MatMul - ~MatMul).this.apply(discrete.matmul.to.lamda)

    Eq <<= Eq[-4].rhs.find(Mul).this.apply(algebra.mul_kroneckerDelta.subs, 1, reverse=True),\
        Eq[-3].rhs.find(Mul).this.apply(algebra.mul_kroneckerDelta.subs, 1, reverse=True),\
        Eq[-2].rhs.find(Mul).this.apply(algebra.mul_kroneckerDelta.subs, 1, reverse=True),\
        Eq[-1].rhs.find(Mul).this.apply(algebra.mul_kroneckerDelta.subs, 1, reverse=True)

    Eq << Eq[-9].subs(*Eq[-8:])

    Eq <<= Eq[-1].find(Lamda).this().find(Element).simplify(),\
        Eq[-1].find(Lamda + ~Lamda).this().find(Element).simplify(),\
        Eq[-1].find((~Lamda) - Lamda).this().find(Element).simplify(),\
        Eq[-1].find(Lamda - ~Lamda).this().find(Element).simplify()

    Eq << Eq[-5].subs(*Eq[-4:])

    Eq <<= Eq[-1].find(Lamda + Lamda).this.apply(algebra.add.to.lamda, deep=True),\
        Eq[-1].find(Lamda - Lamda).this.apply(algebra.add.to.lamda, deep=True),\
        Eq[-1].rhs.args[1].find(Lamda - Lamda).this.apply(algebra.add.to.lamda, deep=True)

    Eq << Eq[-4].subs(*Eq[-3:])

    Eq <<= Eq[-1].find(Mul + Mul).this.apply(algebra.add.to.mul),\
        Eq[-1].find(Mul[KroneckerDelta] - Mul).this.apply(algebra.add.to.mul)

    Eq << Eq[-3].subs(*Eq[-2:])

    Eq <<= Eq[-1].rhs.find(Sin * Sin + Cos * Cos).this.apply(geometry.add.to.cos), \
        Eq[-1].rhs.find(Sin * Cos - Sin * Cos).this.apply(geometry.sub.to.sin)

    Eq << Eq[-3].subs(*Eq[-2:])

    Eq <<= Eq[-1].find(Add).this.apply(algebra.add.to.mul),\
        Eq[-1].find(Sin[~Add]).this.apply(algebra.add.to.mul)

    Eq << Eq[-3].subs(*Eq[-2:])

    Eq << Eq[-1].find(Lamda[-Expr]).this.simplify()

    Eq << Eq[-2].subs(Eq[-1])

    Eq <<= Eq[-1].find(Lamda).this.apply(algebra.lamda.to.mul),\
        Eq[-1].find(-~Lamda).this.apply(algebra.lamda.to.mul)

    Eq << Eq[-1].find(Lamda[KroneckerDelta]).this.apply(algebra.lamda.to.identity)

    Eq << Eq[-4].subs(*Eq[-3:])

    Eq <<= Eq[-1].find(Lamda).this.apply(geometry.lamda.to.cos), Eq[-1].find(Lamda[Sin]).this.apply(geometry.lamda.to.sin)

    Eq << Eq[-1].rhs.find(Lamda).this.apply(algebra.lamda.to.pow)

    j = Eq[-1].lhs.variable
    Eq << Eq[0].subs(k, k - t).this.find(Lamda).limits_subs(i, j).reversed

    Eq.eq_matmul = Eq[-5].subs(*Eq[-4:])

    Eq << Eq[1].subs(k, k - t)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq.eq_matmul, Eq[-1])

    Eq << algebra.cond.imply.all.domain_defined.apply(Eq[-1], k)

    Eq << algebra.all.imply.infer.apply(Eq[-1])

    Eq << Eq[-1].this(t).find(Max).simplify()

    Eq << Eq[-1].this(t).find(Min).simplify()

    Eq << Eq[-1].this.lhs.apply(sets.el_range.given.et)

    Eq << Eq[-1].this(k).find(Less).simplify()

    Eq << Eq[-1].subs(k, j).subs(t, k).subs(j, t)

    Eq << Eq[-1].this.rhs.apply(algebra.eq.imply.eq.transpose)

    Eq << Eq[-1].this.lhs.reversed

    Eq << Eq[-1].this.lhs.apply(algebra.le.given.lt)

    Eq << algebra.cond_piece.given.et.infer.apply(Eq[2])

    
    


if __name__ == '__main__':
    run()
# created on 2023-06-08
# updated on 2023-06-16
