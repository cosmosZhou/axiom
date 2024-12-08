from util import *


@apply
def apply(given, wrt=None):
    from Axiom.Sets.Or.to.In.Piece.two import expr_cond_pair
    or_eqs = given.of(Or)

    return Unequal(Piecewise(*expr_cond_pair(Unequal, or_eqs, wrt, reverse=True)).simplify(), wrt)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    k = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(k,), given=True)
    A, B = Symbol(etype=dtype.real[k], given=True)
    f, g, h = Function(shape=(k,), real=True)
    p = Symbol(shape=(k,), real=True, given=True)
    Eq << apply(Unequal(f(x), p) & Element(x, A) | Unequal(p, g(x)) & Element(x, B - A) | Unequal(p, h(x)) & NotElement(x, A | B), wrt=p)

    Eq << Eq[0].this.find(Element[Complement]).apply(Sets.In_Complement.to.And, simplify=None)

    Eq << Eq[-1].this.find(NotElement[Union]).apply(Sets.NotIn.to.And.split.Union, simplify=None)

    Eq << Eq[-1].apply(Algebra.Or.to.Or.collect, cond=NotElement(x, A))

    Eq << Eq[-1].this.find(Or).apply(Algebra.Or.to.Ne.two, wrt=p)

    Eq << Eq[-1].apply(Algebra.Or.to.Ne.two, wrt=p)

    Eq << Eq[-1].reversed
    Eq << Eq[-1].this.lhs.apply(Algebra.Piece.swap)





if __name__ == '__main__':
    run()

# created on 2020-02-08
# updated on 2023-05-08
from . import two
