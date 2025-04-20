from util import *


@apply
def apply(given, wrt=None):
    from Axiom.Logic.CondIte.of.OrAndS import expr_cond_pair
    or_eqs = given.of(Or)

    return Less(Piecewise(*expr_cond_pair(Less, or_eqs, wrt)).simplify(), wrt)


@prove
def prove(Eq):
    from Axiom import Set, Algebra, Logic

    x = Symbol(real=True, given=True)
    A, B = Symbol(etype=dtype.real, given=True)
    f, g, h = Function(real=True)
    p = Symbol(real=True, given=True)
    Eq << apply(Less(f(x), p) & Element(x, A) | Less(g(x), p) & Element(x, B - A) | Less(h(x), p) & NotElement(x, A | B), wrt=p)

    Eq << Eq[0].this.args[1].args[1].apply(Set.Mem.et.NotMem.of.Mem_SDiff, simplify=None)

    Eq << Eq[-1].this.find(NotElement[Union]).apply(Set.AndNotSMem.of.NotMem_Union, simplify=None)

    Eq << Eq[-1].apply(Logic.OrAndOr.of.OrAnd__OrAnd, cond=NotElement(x, A))

    Eq << Eq[-1].this.find(Or).apply(Algebra.Lt.of.Or.two, wrt=p)

    Eq << Eq[-1].apply(Algebra.Lt.of.Or.two, wrt=p)




if __name__ == '__main__':
    run()

# created on 2019-08-06
# updated on 2023-05-12

from . import two
