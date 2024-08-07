from util import *


@apply
def apply(given, wrt=None):
    from axiom.sets.ou.imply.el.piece.two import expr_cond_pair
    or_eqs = given.of(Or)

    return Greater(Piecewise(*expr_cond_pair(Greater, or_eqs, wrt)).simplify(), wrt)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(real=True, given=True)
    A, B = Symbol(etype=dtype.real, given=True)
    f, g, h = Function(real=True)
    p = Symbol(real=True, given=True)
    Eq << apply(Greater(f(x), p) & Element(x, A) | Greater(g(x), p) & Element(x, B - A) | Greater(h(x), p) & NotElement(x, A | B), wrt=p)

    Eq << Eq[0].this.find(Element[Complement]).apply(sets.el_complement.imply.et, simplify=None)

    Eq << Eq[-1].this.find(NotElement[Union]).apply(sets.notin.imply.et.split.union, simplify=None)

    Eq << Eq[-1].apply(algebra.ou.imply.ou.collect, cond=NotElement(x, A))

    Eq << Eq[-1].this.find(Or).apply(algebra.ou.imply.gt.two, wrt=p)

    Eq << Eq[-1].apply(algebra.ou.imply.gt.two, wrt=p)

    
    


if __name__ == '__main__':
    run()

from . import two
# created on 2020-01-13
# updated on 2023-05-08
