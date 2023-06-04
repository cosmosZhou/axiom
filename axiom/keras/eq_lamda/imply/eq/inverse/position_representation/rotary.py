from util import *


from axiom.keras.eq_lamda.imply.eq.matmul.to.lamda.position_representation.rotary import rotary_matrix, extract

@apply
def apply(eq_R):
    (R, n, d), b, (i, j, k) = extract(eq_R)
    return Equal(R[i].T, R[i] ^ -1)

@prove
def prove(Eq):
    from axiom import keras, algebra, discrete

    #n denotes sequence length (seq_length)
    #b denotes 10000
    n, b = Symbol(integer=True, positive=True)
    #d denotes embedding size which must be even
    d = Symbol(integer=True, positive=True, even=True)
    #i denotes token index
    #j denotes row index
    #k denotes column index
    i, j, k = Symbol(integer=True)
    #R denotes rotary matrix
    R = Symbol(shape=(n, d, d), real=True)
    Eq << apply(Equal(R, rotary_matrix(n, d, b, i, j, k)))

    Eq << keras.eq_lamda.imply.eq.matmul.to.piece.position_representation.rotary.apply(Eq[0])

    Eq << Eq[-1].subs(j, i)

    Eq << Eq[0][0]

    Eq << Eq[-1].this.find(Piecewise).apply(algebra.piece.to.kroneckerDelta)

    Eq << Eq[-1].this.rhs.apply(algebra.lamda_kroneckerDelta.to.identity)

    Eq << Eq[-4].subs(Eq[-1])

    Eq << discrete.eq_matmul.imply.eq.inverse.apply(Eq[-1])

    


if __name__ == '__main__':
    run()
# created on 2023-06-03
