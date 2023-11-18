from util import *


def rotary_matrix(d_r, d_c, b_r, b_c, λ_r, λ_c, θ_r, θ_c, R, i, j, k):
    θ = [θ_r[i], θ_c[j]]
    d = d_r + d_c
    d /= 2
    return Equal(θ_r[i], λ_r * i / b_r ** (2 * Lamda[k:d_r / 2](k) / d_r)), \
        Equal(θ_c[j], λ_c * j / b_c ** (2 * Lamda[k:d_c / 2](k) / d_c)),\
        Equal(R(i, j), BlockMatrix([
            [Identity(d) * cos(θ), -Identity(d) * sin(θ)],
            [Identity(d) * sin(θ),  Identity(d) * cos(θ)]]))
        
def extract(eq_theta_r, eq_theta_c, eq_R):
    from axiom.keras.eq_mul.imply.eq.matmul.position_representation import extract_theta 
    d_r, b_r, λ_r, θ_r, i, k = extract_theta(eq_theta_r)
    d_c, b_c, λ_c, θ_c, j, S[k] = extract_theta(eq_theta_c)
    
    ((θij, S[θij]), (S[θij], S[θij])), Rij = eq_R.of(Equal[BlockMatrix[BlockMatrix[1][Identity * cos[BlockMatrix], -Identity * sin[BlockMatrix]], BlockMatrix[1][Identity * sin[BlockMatrix], Identity * cos[BlockMatrix]]]])
    θ_r[i], θ_c[j] = θij
    return d_r, d_c, θ_r, θ_c, Rij, i, j, k
    

@apply
def apply(eq_theta_r, eq_theta_c, eq_R, i_, j_):
    d_r, d_c, θ_r, θ_c, Rij, i, j, k = extract(eq_theta_r, eq_theta_c, eq_R)
    return Equal(Rij.subs(i, i_).subs(j, j_).T @ Rij, Rij.subs(i, i - i_).subs(j, j - j_))


@prove
def prove(Eq):
    from axiom import keras, discrete, algebra, geometry
    #n denotes sequence length (seq_length)
    #b_r, b_c denotes 10000
    n = Symbol(integer=True, positive=True)
    format_supscript = r"^{\color{magenta} %s}"
    format_r = '%s' + format_supscript % 'r'
    format_c = '%s' + format_supscript % 'c'    
    b_r = Symbol(format_r.replace('^', '_') % 'b', integer=True, positive=True)
    b_c = Symbol(format_c.replace('^', '_') % 'b', integer=True, positive=True)
        
    #d, d_r, d_c denotes embedding size which must be divisible by 2, under the condition that d = d_r + d_c
    d_r = Symbol(format_r % 'd', integer=True, positive=True, even=True)
    d_c = Symbol(format_c % 'd', integer=True, positive=True, even=True)
    d = d_r + d_c
    #x_k denotes token embedding at index k (ie, x denotes sentence embedding)
    x = Symbol(shape=(n, d), real=True)
    #R denotes rotary matrix function
    R = Function(shape=(d, d), real=True)
    θ_r = Symbol(format_r % "θ", shape=(n, d_r / 2), real=True)
    θ_c = Symbol(format_c % "θ", shape=(n, d_c / 2), real=True)
    #t denotes time step
    #i denotes row index, j denotes column index
    i, j, t, k = Symbol(integer=True)
    #r, c denote the row index and column index respectively, each token has a (r[t], c[t]) two-demensional index
    r, c = Symbol(integer=True, shape=(n,))
    #λ denotes scaling factor, default to 1
    λ_r = Symbol(format_r % "λ", real=True)
    λ_c = Symbol(format_c % "λ", real=True)

    i_quote, j_quote = Symbol(integer=True)
    Eq << apply(*rotary_matrix(d_r, d_c, b_r, b_c, λ_r, λ_c, θ_r, θ_c, R, i, j, k), i_quote, j_quote)

    Eq << keras.eq_mul.imply.eq.matmul.position_representation.apply(Eq[0], i_quote)

    Eq << keras.eq_mul.imply.eq.matmul.position_representation.apply(Eq[1], j_quote)

    Eq << discrete.eq_matmul.eq_matmul.imply.eq.matmul.apply(*Eq[-2:])

    Eq << Eq[-1].find(ZeroMatrix).this.apply(algebra.expr.to.block, d_r / 2, d_c / 2)

    Eq << Eq[-1].T

    Eq << Eq[-3].subs(*Eq[-2:])

    Ir = Identity(d_r / 2)
    Ic = Identity(d_c / 2)
    Zrc = ZeroMatrix(d_r / 2, d_c / 2)
    Zrr = ZeroMatrix(d_r / 2, d_r / 2)
    Zcr = Zrc.T
    Zcc = ZeroMatrix(d_c / 2, d_c / 2)
    #suppose I Matrix is as follows:
    #I = [
    #[ Ir, Zrr, Zrc, Zrc],
    #[Zrr,  Ir, Zrc, Zrc],
    #[Zcr, Zcr,  Ic, Zcc],
    #[Zcr, Zcr, Zcc,  Ic]]
    #swap the 1st and 2nd rows of I Matrix, we get the row transformation
    D_r = [
        [ Ir, Zrr, Zrc, Zrc],
        [Zcr, Zcr,  Ic, Zcc],
        [Zrr,  Ir, Zrc, Zrc],
        [Zcr, Zcr, Zcc,  Ic]]
    Eq << discrete.eq.imply.eq.rmatmul.apply(Eq[-1], D_r)

    Eq << Eq[-1].this.lhs.args[:2].apply(discrete.matmul.to.block, deep=True)

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.block, deep=True)

    #swap the 1st and 2nd columns of I Matrix, we get the column transformation
    D_c = [
        [ Ir, Zrc, Zrr, Zrc],
        [Zrr, Zrc,  Ir, Zrc],
        [Zcr,  Ic, Zcr, Zcc],
        [Zcr, Zcc, Zcr,  Ic]]
    Eq << discrete.eq.imply.eq.matmul.apply(Eq[-1], D_c)

    Eq << Eq[-1].this.lhs.args[-2:].apply(discrete.matmul.to.block, deep=True)

    Eq.eq_matmul = Eq[-1].this.rhs.apply(discrete.matmul.to.block, deep=True)

    Eq <<= (Eq.eq_matmul.lhs.args[0] @ D_c).this.apply(discrete.matmul.to.block, deep=True),  (D_r @ Eq.eq_matmul.lhs.args[1]).this.apply(discrete.matmul.to.block, deep=True)

    Eq << Eq[-2] @ Eq[-1]

    Eq << Eq[-1].this.lhs.args[1:3].apply(discrete.matmul.to.block, deep=True)

    Eq << Eq[-1].this.find(BlockMatrix[2]).apply(algebra.block.to.identity)

    Eq.eq_matmul = algebra.eq.eq.imply.eq.transit.apply(Eq.eq_matmul, Eq[-1])

    Eq << Eq[2].subs(i, i_quote).subs(j, j_quote).T @ Eq[2]

    Eq.identity = Eq[-1].find(Identity).this.apply(algebra.expr.to.block, d_r / 2, d_r / 2)

    Eq <<= Eq[-1].find(cos).this.apply(geometry.cos.to.block), Eq[-1].find(sin).this.apply(geometry.sin.to.block), \
        Eq[-1].find(BlockMatrix[2]).find(cos).this.apply(geometry.cos.to.block), Eq[-1].find(BlockMatrix[2]).find(sin).this.apply(geometry.sin.to.block)

    Eq << Eq[-5].subs(*Eq[-4:], Eq.identity)

    Eq <<= Eq[-1].find(Mul).this.apply(algebra.mul.to.block),\
        Eq[-1].find(Mul[2]).this.apply(algebra.mul.to.block),\
        Eq[-1].find(BlockMatrix[2]).find(Mul).this.apply(algebra.mul.to.block),\
        Eq[-1].find(BlockMatrix[2]).args[1].find(Mul).this.apply(algebra.mul.to.block)

    Eq << Eq[-5].subs(*Eq[-4:])

    Eq <<= Eq[-1].find(-BlockMatrix).this.apply(algebra.mul.to.block), \
        Eq[-1].find(BlockMatrix[2]).find(-BlockMatrix).this.apply(algebra.mul.to.block)

    Eq << Eq[-3].subs(*Eq[-2:])

    Eq.eq_matmul = algebra.eq.eq.imply.eq.transit.apply(Eq[-1], Eq.eq_matmul)

    Eq << Eq[2].subs(i, i - i_quote).subs(j, j - j_quote)

    Eq <<= Eq[-1].find(cos).this.apply(geometry.cos.to.block), Eq[-1].find(sin).this.apply(geometry.sin.to.block)

    Eq << Eq[-3].subs(*Eq[-2:], Eq.identity)

    Eq <<= Eq[-1].rhs.find(Mul).this.apply(algebra.mul.to.block),\
        Eq[-1].rhs.args[1].find(Mul).this.apply(algebra.mul.to.block)

    Eq << Eq[-3].subs(*Eq[-2:])

    Eq << Eq[-1].this.find(-BlockMatrix).apply(algebra.mul.to.block)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq.eq_matmul, Eq[-1])

    
    


if __name__ == '__main__':
    run()
# created on 2023-09-16
# updated on 2023-09-18
