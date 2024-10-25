from util import *


@apply
def apply(self, index=-1):
    a, b = self.of(Range)
    args = b.of(Min)
    former = Min(*args[:index])
    latter = Min(*args[index:])
    return Equal(self, Intersection(Range(a, former), Range(a, latter), evaluate=False))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, c = Symbol(integer=True)
    Eq << apply(Range(a, Min(b, c)))

    Eq << sets.eq.of.et.infer.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(sets.el_range.then.et), Eq[-1].this.rhs.apply(sets.el_range.of.et)

    Eq <<= Eq[-2].this.find(Less).apply(algebra.lt_min.then.et.lt), Eq[-1].this.find(Less).apply(algebra.lt_min.of.et.lt)

    Eq <<= Eq[-2].this.find(Element).apply(sets.el_intersect.of.et, simplify=None), Eq[-1].this.find(Element).apply(sets.el_intersect.then.et, simplify=None)

    Eq <<= Eq[-2].this.find(Element).apply(sets.el_range.of.et), Eq[-1].this.find(Element).apply(sets.el_range.then.et)

    Eq <<= Eq[-2].this.find(Element).apply(sets.el_range.of.et), Eq[-1].this.find(Element).apply(sets.el_range.then.et)




if __name__ == '__main__':
    run()
# created on 2022-01-01

