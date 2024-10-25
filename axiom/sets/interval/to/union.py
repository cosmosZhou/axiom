from util import *


@apply
def apply(self, pivot=None):
    a, b = self.of(Interval)
    assert self.conditionally_contains(pivot)
    A = self.copy(stop=pivot, right_open=True)
    B = self.copy(start=pivot, left_open=False)
    return Equal(self, Union(A, B, evaluate=False))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b = Symbol(integer=True)
    c = Symbol(domain=Interval(a, b, left_open=True, right_open=True))
    Eq << apply(Interval(a, b), c)

    Eq << sets.eq.of.et.infer.apply(Eq[0])

    Eq <<= Eq[-2].this.find(Element[Interval]).apply(sets.el_interval.to.et), Eq[-1].this.find(Element[Interval]).apply(sets.el_interval.to.et)

    Eq <<= Eq[-2].this.find(Element[Union]).apply(sets.el_union.to.ou), Eq[-1].this.find(Element[Union]).apply(sets.el_union.to.ou)

    Eq <<= Eq[-2].this.find(Element).apply(sets.el_interval.to.et), Eq[-1].this.find(Element).apply(sets.el_interval.to.et)

    Eq <<= Eq[-2].this.find(Element).apply(sets.el_interval.to.et), Eq[-1].this.find(Element).apply(sets.el_interval.to.et)

    Eq << algebra.infer_ou.of.et.infer.apply(Eq[-1])

    Eq <<= algebra.infer_et.of.infer.delete.apply(Eq[-2]), algebra.infer_et.of.infer.delete.apply(Eq[-1], 0)

    Eq << Eq[-1].this.lhs.apply(algebra.ge.then.ge.relax, a)

    Eq << Eq[-2].this.lhs.apply(algebra.lt.then.lt.relax, b)

    Eq << algebra.infer.of.ou.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-04-18
