from util import *


@apply
def apply(self):
    from Axiom.Algebra.Cond_Piece.equ.And.Imply import piecewise_to_et
    return piecewise_to_et(self)



@prove
def prove(Eq):
    from Axiom import Algebra

    x, p = Symbol(real=True, shape=(), given=True)
    A, B = Symbol(etype=dtype.real, given=True)
    f, g, h = Function(shape=(), real=True)
    Eq << apply(Equal(p, Piecewise((f(x), Element(x, A)), (g(x), Element(x, B)), (h(x), True))))

    Eq << Algebra.Cond_Piece.of.Or.apply(Eq[0])

    Eq << ~Eq[-1]

    Eq << Algebra.Imply.to.Or.apply(Eq[1])

    Eq <<= Eq[-2] & Eq[-1]

    Eq << Algebra.And.to.Or.apply(Eq[-1])

    Eq << Algebra.Imply.to.Or.apply(Eq[2])

    Eq <<= Eq[-2] & Eq[-1]

    Eq << Algebra.And.to.Or.apply(Eq[-1])

    Eq << Algebra.Imply.to.Or.apply(Eq[3])

    Eq <<= Eq[-2] & Eq[-1]

    Eq << Algebra.And.to.Or.apply(Eq[-1])

    Eq << Algebra.And.to.Or.apply(Eq[-1])

    Eq << Algebra.And.to.Or.apply(Eq[-1])

    Eq << Algebra.And.to.Or.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-04-25
# updated on 2023-04-29
