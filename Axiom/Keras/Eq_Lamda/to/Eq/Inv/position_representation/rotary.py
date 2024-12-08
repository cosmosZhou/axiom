from util import *


@apply
def apply(eq_R):
    from Axiom.Keras.Eq_Lamda.to.Dot.eq.Lamda.position_representation.rotary import extract
    (Ri, d), b, (i, j, k) = extract(eq_R)
    return Equal(Ri.T, Ri ^ -1)

@prove
def prove(Eq):
    from Axiom import Keras, Algebra, Discrete
    from Axiom.Keras.Eq_Lamda.to.Dot.eq.Lamda.position_representation.rotary import rotary_matrix
    # b denotes 10000
    b = Symbol(integer=True, positive=True)
    # d denotes embedding size which must be even
    d = Symbol(integer=True, positive=True, even=True)
    # i denotes token index
    # j denotes row index
    # k denotes column index
    i, j, k = Symbol(integer=True)
    # R denotes rotary matrix
    R = Function(shape=(d, d), real=True)
    Eq << apply(Equal(R(i), rotary_matrix(d, b, i, j, k)))

    Eq << Keras.Eq_Lamda.to.Eq.Dot.position_representation.rotary.apply(Eq[0])

    Eq << Eq[-1].subs(j, i)

    Eq << Eq[0].subs(i, 0)

    Eq << Eq[-1].this.find(Piecewise).apply(Algebra.Piece.eq.Delta)

    Eq << Eq[-1].this.rhs.apply(Algebra.Lamda.Delta.eq.Identity)

    Eq << Eq[-4].subs(Eq[-1])

    Eq << Discrete.Eq_Dot.to.Eq.Inv.apply(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2023-06-03
# updated on 2023-09-16
