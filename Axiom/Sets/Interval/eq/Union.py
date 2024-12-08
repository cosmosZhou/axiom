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
    from Axiom import Sets, Algebra

    a, b = Symbol(integer=True)
    c = Symbol(domain=Interval(a, b, left_open=True, right_open=True))
    Eq << apply(Interval(a, b), c)

    Eq << Sets.Eq.of.And.Imply.apply(Eq[0])

    Eq <<= Eq[-2].this.find(Element[Interval]).apply(Sets.In_Interval.equ.And), Eq[-1].this.find(Element[Interval]).apply(Sets.In_Interval.equ.And)

    Eq <<= Eq[-2].this.find(Element[Union]).apply(Sets.In_Union.equ.Or), Eq[-1].this.find(Element[Union]).apply(Sets.In_Union.equ.Or)

    Eq <<= Eq[-2].this.find(Element).apply(Sets.In_Interval.equ.And), Eq[-1].this.find(Element).apply(Sets.In_Interval.equ.And)

    Eq <<= Eq[-2].this.find(Element).apply(Sets.In_Interval.equ.And), Eq[-1].this.find(Element).apply(Sets.In_Interval.equ.And)

    Eq << Algebra.Imply_Or.of.And.Imply.apply(Eq[-1])

    Eq <<= Algebra.Imply_And.of.Imply.delete.apply(Eq[-2]), Algebra.Imply_And.of.Imply.delete.apply(Eq[-1], 0)

    Eq << Eq[-1].this.lhs.apply(Algebra.Ge.to.Ge.relax, a)

    Eq << Eq[-2].this.lhs.apply(Algebra.Lt.to.Lt.relax, b)

    Eq << Algebra.Imply.of.Or.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-04-18
