from util import *


@apply
def apply(given):
    from Axiom.Algebra.Cond_Piece.to.Or import piecewise_to_ou
    return piecewise_to_ou(given)


@prove
def prove(Eq):
    from Axiom import Algebra

    k = Symbol(integer=True, positive=True)
    x, p = Symbol(real=True, shape=(k,), given=True)
    A, B = Symbol(etype=dtype.real[k], given=True)
    f, g, h = Function(shape=(k,), real=True)
    Eq << apply(Equal(p, Piecewise((f(x), Element(x, A)), (g(x), Element(x, B)), (h(x), True))))

    Eq << Algebra.Or.to.Eq.Piece.apply(Eq[1], p).reversed




if __name__ == '__main__':
    run()
# created on 2019-04-25
# updated on 2023-04-29
