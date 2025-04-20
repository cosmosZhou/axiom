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
    from Axiom import Set, Algebra, Logic

    a, b = Symbol(integer=True)
    c = Symbol(domain=Interval(a, b, left_open=True, right_open=True))
    Eq << apply(Interval(a, b), c)

    Eq << Set.Eq.given.And.Imp.apply(Eq[0])

    Eq <<= Eq[-2].this.find(Element[Interval]).apply(Set.Mem_Icc.Is.And), Eq[-1].this.find(Element[Interval]).apply(Set.Mem_Icc.Is.And)

    Eq <<= Eq[-2].this.find(Element[Union]).apply(Set.Mem_Union.Is.Or), Eq[-1].this.find(Element[Union]).apply(Set.Mem_Union.Is.Or)

    Eq <<= Eq[-2].this.find(Element).apply(Set.Mem_Icc.Is.And), Eq[-1].this.find(Element).apply(Set.Mem_Icc.Is.And)

    Eq <<= Eq[-2].this.find(Element).apply(Set.Mem_Icc.Is.And), Eq[-1].this.find(Element).apply(Set.Mem_Icc.Is.And)

    Eq << Logic.ImpOr.given.Imp.Imp.apply(Eq[-1])

    Eq <<= Logic.Imp_And.given.Imp.delete.apply(Eq[-2]), Logic.Imp_And.given.Imp.delete.apply(Eq[-1], 0)

    Eq << Eq[-1].this.lhs.apply(Algebra.Ge.of.Ge.relax, a)

    Eq << Eq[-2].this.lhs.apply(Algebra.Lt.of.Lt.relax, b)

    Eq << Logic.Imp.given.Or_Not.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-04-18
