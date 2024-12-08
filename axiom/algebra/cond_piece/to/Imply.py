from util import *


@apply
def apply(self, index=0):
    from Axiom.Algebra.Cond_Piece.equ.And.Imply import piecewise_to_et
    return piecewise_to_et(self, True)[index]



@prove
def prove(Eq):
    from Axiom import Algebra

    x, p = Symbol(real=True, shape=())
    A, B = Symbol(etype=dtype.real)
    f, g, h = Function(shape=(), real=True)
    Eq << apply(Equal(p, Piecewise((f(x), Element(x, A)), (g(x), Element(x, B)), (h(x), True))))

    Eq << Algebra.Cond_Piece.to.And.Imply.apply(Eq[0])




if __name__ == '__main__':
    run()
# created on 2023-06-06
