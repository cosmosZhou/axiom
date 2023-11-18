from util import *


def eq_theta(θ, d, b, k, i, λ=1): 
    return Equal(θ[k], λ * k / b ** (Lamda[i:d / 2](i) / (d / 2)))

def rotary_def(θ, d, k):
    return BlockMatrix([
        [Identity(d / 2) * cos(θ[k]), -Identity(d / 2) * sin(θ[k])],
        [Identity(d / 2) * sin(θ[k]), Identity(d / 2) * cos(θ[k])]])
        
def rotary_matrix(R, θ, d, b, k, i, λ=1):
    return eq_theta(θ, d, b, k, i, λ), Equal(R(k), rotary_def(θ, d, k))

def extract_theta(eq_theta):
    (tλ, (b, ((k, limit_k), d))), (θ, t) = eq_theta.of(Equal[Expr / Symbol ** (2 * Lamda / Symbol), Indexed])
    assert d.is_even
    S[k], S[0], S[d / 2] = limit_k
    λ = tλ / t
    return d, b, λ, θ, t, k

def extract(eq_theta, eq_R):
    d, b, λ, θ, k, i = extract_theta(eq_theta)
    ((cos, sin), (S[-sin], S[cos])), Rk = eq_R.of(Equal[BlockMatrix[BlockMatrix[1], BlockMatrix[1]]])
    S[θ[k]] = cos.of(Cos[Expr] * Identity)
    S[θ[k]] = sin.of(-Identity * Sin[Expr])
    alpha = BlockMatrix(θ[k], θ[k])
    
    return Rk, d, alpha, θ, b, k, i, λ 

@apply
def apply(eq_theta, t):
    d, b, λ, θ, k, i = extract_theta(eq_theta)
    Rk = rotary_def(θ, d, k)
    return Equal(Rk.subs(k, t).T @ Rk, Rk.subs(k, k - t))

@prove
def prove(Eq):
    from axiom import discrete, algebra, geometry

    # n denotes sequence length (seq_length)
    # b denotes 10000
    n, b = Symbol(integer=True, positive=True)
    # d denotes embedding size which must be even
    d = Symbol(integer=True, positive=True, even=True)
    θ = Symbol(shape=(n, d / 2), real=True)
    # k, t denote token index
    # i denotes row index
    i, k, t = Symbol(integer=True)
    # λ denotes scaling factor
    λ = Symbol(real=True)
    Eq << apply(eq_theta(θ, d, b, k, i, λ), t)

    Eq << Eq[1].subs(Eq[0]).subs(Eq[0].subs(k, t))

    Eq << Eq[-1].this.lhs.apply(discrete.matmul.to.block, deep=True)

    Eq <<= Eq[-1].lhs.find(MatMul).this.apply(discrete.matmul.to.lamda),\
        Eq[-1].lhs.find(MatMul[2]).this.apply(discrete.matmul.to.lamda),\
        Eq[-1].lhs.find((~MatMul) - MatMul).this.apply(discrete.matmul.to.lamda),\
        Eq[-1].lhs.find(MatMul - ~MatMul).this.apply(discrete.matmul.to.lamda)

    Eq <<= Eq[-4].rhs.find(Mul).this.apply(algebra.mul.delta.subs, 1, reverse=True),\
        Eq[-3].rhs.find(Mul).this.apply(algebra.mul.delta.subs, 1, reverse=True),\
        Eq[-2].rhs.find(Mul).this.apply(algebra.mul.delta.subs, 1, reverse=True),\
        Eq[-1].rhs.find(Mul).this.apply(algebra.mul.delta.subs, 1, reverse=True)

    Eq << Eq[-9].subs(*Eq[-8:])

    Eq <<= Eq[-1].find(Lamda).this().find(Element).simplify(),\
        Eq[-1].find(Lamda + ~Lamda).this().find(Element).simplify(),\
        Eq[-1].find((~Lamda) - Lamda).this().find(Element).simplify(),\
        Eq[-1].find(Lamda - ~Lamda).this().find(Element).simplify()

    Eq << Eq[-5].subs(*Eq[-4:])

    Eq <<= Eq[-1].find(Lamda + Lamda).this.apply(algebra.add.to.lamda, deep=True),\
        Eq[-1].find(Lamda - Lamda).this.apply(algebra.add.to.lamda, deep=True),\
        Eq[-1].lhs.args[1].find(Lamda - Lamda).this.apply(algebra.add.to.lamda, deep=True)

    Eq << Eq[-4].subs(*Eq[-3:])

    Eq <<= Eq[-1].find(Mul + Mul).this.apply(algebra.add.to.mul),\
        Eq[-1].find(Mul[KroneckerDelta] - Mul).this.apply(algebra.add.to.mul)
    Eq << Eq[-3].subs(*Eq[-2:])
    Eq <<= Eq[-1].lhs.find(Sin * Sin + Cos * Cos).this.apply(geometry.add.to.cos), \
        Eq[-1].lhs.find(Sin * Cos - Sin * Cos).this.apply(geometry.sub.to.sin)

    Eq << Eq[-3].subs(*Eq[-2:])

    Eq <<= Eq[-1].lhs.find(Add).this.apply(algebra.add.to.mul),\
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

    Eq << Eq[-5].subs(*Eq[-4:])

    
    


if __name__ == '__main__':
    run()
# created on 2023-09-16
# updated on 2023-09-20
