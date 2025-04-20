from util import *


@apply
def apply(given, wrt=None):
    from Axiom.Logic.CondIte.of.OrAndS import expr_cond_pair
    or_eqs = given.of(Or)

    return Unequal(Piecewise(*expr_cond_pair(Unequal, or_eqs, wrt, reverse=True)).simplify(), wrt)


@prove
def prove(Eq):
    from Axiom import Set, Algebra, Logic

    k = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(k,), given=True)
    A, B = Symbol(etype=dtype.real[k], given=True)
    f, g, h = Function(shape=(k,), real=True)
    p = Symbol(shape=(k,), real=True, given=True)
    Eq << apply(Unequal(f(x), p) & Element(x, A) | Unequal(p, g(x)) & Element(x, B - A) | Unequal(p, h(x)) & NotElement(x, A | B), wrt=p)

    Eq << Eq[0].this.find(Element[Complement]).apply(Set.Mem.et.NotMem.of.Mem_SDiff, simplify=None)

    Eq << Eq[-1].this.find(NotElement[Union]).apply(Set.AndNotSMem.of.NotMem_Union, simplify=None)

    Eq << Eq[-1].apply(Logic.OrAndOr.of.OrAnd__OrAnd, cond=NotElement(x, A))

    Eq << Eq[-1].this.find(Or).apply(Algebra.Ne.of.Or.two, wrt=p)

    Eq << Eq[-1].apply(Algebra.Ne.of.Or.two, wrt=p)

    Eq << Eq[-1].reversed
    Eq << Eq[-1].this.lhs.apply(Logic.Ite__Ite.eq.IteAnd_Not__Ite)





if __name__ == '__main__':
    run()

# created on 2020-02-08
# updated on 2023-05-08

from . import two
