from util import *


@apply
def apply(given, wrt=None):
    from Axiom.Sets.Or.to.In.Piece.two import expr_cond_pair
    or_eqs = given.of(Or)

    return Element(Piecewise(*expr_cond_pair(Element, or_eqs, wrt)).simplify(), wrt)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    k = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(k,), given=True)
    A, B, S = Symbol(etype=dtype.real[k], given=True)
    f, g, h = Function(shape=(k,), real=True)
    Eq << apply(Element(f(x), S) & Element(x, A) | Element(g(x), S) & Element(x, B - A) | Element(h(x), S) & NotElement(x, A | B), wrt=S)

    Eq << Eq[0].this.find(Element[Complement]).apply(Sets.In_Complement.to.And, simplify=None)

    Eq << Eq[-1].this.find(NotElement[Union]).apply(Sets.NotIn.to.And.split.Union, simplify=None)

    Eq << Eq[-1].apply(Algebra.Or.to.Or.collect, cond=NotElement(x, A))

    Eq << Eq[-1].this.find(Or).apply(Sets.Or.to.In.Piece.two, wrt=S)

    Eq << Eq[-1].apply(Sets.Or.to.In.Piece.two, wrt=S)





if __name__ == '__main__':
    run()


# created on 2018-03-07
# updated on 2023-05-14

from . import rhs
from . import two
