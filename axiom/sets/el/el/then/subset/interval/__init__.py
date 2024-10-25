from util import *


@apply
def apply(contains1, contains2):
    x, A = contains1.of(Element)
    y, S[A] = contains2.of(Element)

    return Subset(Interval(x, y), A)


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, x, y = Symbol(real=True, given=True)
    S = Interval(a, b, left_open=True)
    Eq << apply(Element(x, S), Element(y, S))

    Eq << sets.subset.of.all_el.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(sets.el_interval.of.et)

    Eq << algebra.all.of.ou.apply(Eq[-1])

    Eq << Eq[-1].this.find(NotElement).apply(sets.notin_interval.of.ou)

    Eq << ~Eq[-1]

    Eq << Eq[-1].this.expr.apply(algebra.et.then.ou, simplify=None)

    Eq << Eq[-1].this.expr.args[0].apply(algebra.et.then.et.delete, index=-1, simplify=None)

    Eq << Eq[-1].this.expr.args[0].apply(algebra.gt.le.then.lt.trans)

    Eq << Eq[-1].this.args[1].expr.apply(algebra.et.then.et.delete, index=1)

    Eq << Eq[-1].this.args[1].expr.apply(algebra.le.ge.then.le.trans)

    Eq << ~Eq[-1]

    Eq <<= sets.el_interval.then.et.apply(Eq[0]), sets.el_interval.then.et.apply(Eq[1])

    Eq <<= Eq[-1] & Eq[-4]

    Eq << Eq[-1].this.args[1].reversed




if __name__ == '__main__':
    run()
from . import right_open
from . import left_open
# created on 2020-03-31
# updated on 2023-05-20
