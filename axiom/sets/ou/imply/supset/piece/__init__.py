from util import *


@apply
def apply(given, wrt=None):
    from axiom.sets.ou.imply.el.piece.two import expr_cond_pair
    or_eqs = given.of(Or)

    return Supset(Piecewise(*expr_cond_pair(Supset, or_eqs, wrt)).simplify(), wrt)


@prove
def prove(Eq):
    from axiom import sets, algebra

    k = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(k,), given=True)
    A, B, S = Symbol(etype=dtype.real[k], given=True)
    f, g, h = Function(etype=dtype.real[k])
    Eq << apply(Supset(f(x), S) & Element(x, A) | Supset(g(x), S) & Element(x, B - A) | Supset(h(x), S) & NotElement(x, A | B), wrt=S)

    Eq << Eq[0].this.find(Element[Complement]).apply(sets.el_complement.imply.et, simplify=None)

    Eq << Eq[-1].this.find(NotElement[Union]).apply(sets.notin.imply.et.split.union, simplify=None)

    Eq << Eq[-1].apply(algebra.ou.imply.ou.collect, cond=NotElement(x, A))

    Eq << Eq[-1].this.find(Or).apply(sets.ou.imply.supset.piece.two, wrt=S)

    Eq << Eq[-1].apply(sets.ou.imply.supset.piece.two, wrt=S)

    


if __name__ == '__main__':
    run()

from . import two
# created on 2021-06-15
# updated on 2023-05-14
