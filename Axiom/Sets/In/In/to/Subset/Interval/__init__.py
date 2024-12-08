from util import *


@apply
def apply(contains1, contains2):
    x, A = contains1.of(Element)
    y, S[A] = contains2.of(Element)

    return Subset(Interval(x, y), A)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    a, b, x, y = Symbol(real=True, given=True)
    S = Interval(a, b, left_open=True)
    Eq << apply(Element(x, S), Element(y, S))

    Eq << Sets.Subset.of.All_In.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(Sets.In_Interval.of.And)

    Eq << Algebra.All.of.Or.apply(Eq[-1])

    Eq << Eq[-1].this.find(NotElement).apply(Sets.NotIn_Interval.of.Or)

    Eq << ~Eq[-1]

    Eq << Eq[-1].this.expr.apply(Algebra.And.to.Or, simplify=None)

    Eq << Eq[-1].this.expr.args[0].apply(Algebra.And.to.And.delete, index=-1, simplify=None)

    Eq << Eq[-1].this.expr.args[0].apply(Algebra.Gt.Le.to.Lt.trans)

    Eq << Eq[-1].this.args[1].expr.apply(Algebra.And.to.And.delete, index=1)

    Eq << Eq[-1].this.args[1].expr.apply(Algebra.Le.Ge.to.Le.trans)

    Eq << ~Eq[-1]

    Eq <<= Sets.In_Interval.to.And.apply(Eq[0]), Sets.In_Interval.to.And.apply(Eq[1])

    Eq <<= Eq[-1] & Eq[-4]

    Eq << Eq[-1].this.args[1].reversed




if __name__ == '__main__':
    run()
# created on 2020-03-31
# updated on 2023-05-20

from . import right_open
from . import left_open
