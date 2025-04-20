from util import *


@apply
def apply(self, index=-1):
    a, b = self.of(Range)
    args = a.of(Min)
    former = Min(*args[:index])
    latter = Min(*args[index:])
    return Equal(self, Union(Range(former, b), Range(latter, b), evaluate=False))


@prove
def prove(Eq):
    from Axiom import Set, Algebra

    a, b, c = Symbol(integer=True)
    Eq << apply(Range(Min(b, c), a))

    Eq << Set.Eq.given.And.Imp.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(Set.And.of.Mem_Range), Eq[-1].this.rhs.apply(Set.Mem_Range.given.And)

    Eq <<= Eq[-2].this.find(GreaterEqual).apply(Algebra.Or.Ge.of.Ge_Min), Eq[-1].this.find(GreaterEqual).apply(Algebra.Ge_Min.given.Or.Ge)

    Eq <<= Eq[-2].this.find(Element).apply(Set.Mem_Union.given.OrMemS, simplify=None), Eq[-1].this.find(Element).apply(Set.Or.of.Mem_Union, simplify=None)

    Eq <<= Eq[-2].this.find(Element).apply(Set.Mem_Range.given.And), Eq[-1].this.find(Element).apply(Set.And.of.Mem_Range)

    Eq <<= Eq[-2].this.find(Element).apply(Set.Mem_Range.given.And), Eq[-1].this.find(Element).apply(Set.And.of.Mem_Range)




if __name__ == '__main__':
    run()
# created on 2022-01-08
