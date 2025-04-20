from util import *


@apply
def apply(contains1, contains2):
    x, A = contains1.of(Element)
    y, S[A] = contains2.of(Element)

    return Subset(Interval(x, y), A)


@prove
def prove(Eq):
    from Axiom import Set, Algebra, Logic

    a, b, x, y = Symbol(real=True, given=True)
    S = Interval(a, b, left_open=True)
    Eq << apply(Element(x, S), Element(y, S))

    Eq << Set.Subset.given.All_Mem.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(Set.Mem_Icc.given.And)

    Eq << Algebra.All.given.Or.apply(Eq[-1])

    Eq << Eq[-1].this.find(NotElement).apply(Set.NotMem_Icc.given.Or)

    Eq << ~Eq[-1]

    Eq << Eq[-1].this.expr.apply(Logic.OrAndS.of.And_Or, simplify=None)

    Eq << Eq[-1].this.expr.args[0].apply(Algebra.And.of.And.delete, index=-1, simplify=None)

    Eq << Eq[-1].this.expr.args[0].apply(Algebra.Lt.of.Gt.Le)

    Eq << Eq[-1].this.args[1].expr.apply(Algebra.And.of.And.delete, index=1)

    Eq << Eq[-1].this.args[1].expr.apply(Algebra.Le.of.Le.Ge)

    Eq << ~Eq[-1]

    Eq <<= Set.And.of.Mem_Icc.apply(Eq[0]), Set.And.of.Mem_Icc.apply(Eq[1])

    Eq <<= Eq[-1] & Eq[-4]

    Eq << Eq[-1].this.args[1].reversed




if __name__ == '__main__':
    run()
# created on 2020-03-31
# updated on 2023-05-20

from . import right_open
from . import left_open
