from util import *


@apply
def apply(given, wrt=None):
    from Axiom.Logic.CondIte.of.OrAndS import expr_cond_pair
    or_eqs = given.of(Or)

    return NotElement(wrt, Piecewise(*expr_cond_pair(NotElement, or_eqs, wrt, reverse=True)).simplify())


@prove
def prove(Eq):
    from Axiom import Set, Algebra, Logic

    k = Symbol(integer=True, positive=True)
    x, y = Symbol(real=True, shape=(k,), given=True)
    A, B = Symbol(etype=dtype.real[k], given=True)
    f, g, h = Function(etype=dtype.real[k])
    Eq << apply(NotElement(y, f(x)) & Element(x, A) | NotElement(y, g(x)) & Element(x, B - A) | NotElement(y, h(x)) & NotElement(x, A | B), wrt=y)

    Eq << Eq[0].this.find(Element[Complement]).apply(Set.Mem.et.NotMem.of.Mem_SDiff, simplify=None)

    Eq << Eq[-1].this.find(NotElement[Union]).apply(Set.AndNotSMem.of.NotMem_Union, simplify=None)

    Eq << Eq[-1].apply(Logic.OrAndOr.of.OrAnd__OrAnd, cond=NotElement(x, A))

    Eq << Eq[-1].this.find(Or).apply(Set.NotMem.Ite.of.Or.rhs.two, wrt=y)

    Eq << Eq[-1].apply(Set.NotMem.Ite.of.Or.rhs.two, wrt=y)





if __name__ == '__main__':
    run()
# created on 2021-06-10
# updated on 2023-05-14

from . import two
