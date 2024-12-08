from util import *


@apply
def apply(given, wrt=None):
    from Axiom.Sets.Or.to.In.Piece.two import expr_cond_pair
    or_eqs = given.of(Or)

    return Less(Piecewise(*expr_cond_pair(Less, or_eqs, wrt)).simplify(), wrt)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x = Symbol(real=True, given=True)
    A, B = Symbol(etype=dtype.real, given=True)
    f, g, h = Function(real=True)
    p = Symbol(real=True, given=True)
    Eq << apply(Less(f(x), p) & Element(x, A) | Less(g(x), p) & Element(x, B - A) | Less(h(x), p) & NotElement(x, A | B), wrt=p)

    Eq << Eq[0].this.args[1].args[1].apply(Sets.In_Complement.to.And, simplify=None)

    Eq << Eq[-1].this.find(NotElement[Union]).apply(Sets.NotIn.to.And.split.Union, simplify=None)

    Eq << Eq[-1].apply(Algebra.Or.to.Or.collect, cond=NotElement(x, A))

    Eq << Eq[-1].this.find(Or).apply(Algebra.Or.to.Lt.two, wrt=p)

    Eq << Eq[-1].apply(Algebra.Or.to.Lt.two, wrt=p)




if __name__ == '__main__':
    run()

# created on 2019-08-06
# updated on 2023-05-12

from . import two
