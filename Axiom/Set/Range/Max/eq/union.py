from util import *


@apply
def apply(self, index=-1):
    a, b = self.of(Range)
    args = b.of(Max)
    former = Max(*args[:index])
    latter = Max(*args[index:])
    return Equal(self, Union(Range(a, former), Range(a, latter), evaluate=False))


@prove
def prove(Eq):
    from Axiom import Set, Algebra

    a, b, c = Symbol(integer=True)
    Eq << apply(Range(a, Max(b, c)))

    Eq << Set.Eq.given.And.Imp.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(Set.And.of.Mem_Range), Eq[-1].this.rhs.apply(Set.Mem_Range.given.And)

    Eq <<= Eq[-2].this.find(Less).apply(Algebra.Or.Lt.of.Lt_Max), Eq[-1].this.find(Less).apply(Algebra.Lt_Max.given.Or.Lt)

    Eq <<= Eq[-2].this.find(Element).apply(Set.Mem_Union.given.OrMemS, simplify=None), Eq[-1].this.find(Element).apply(Set.Or.of.Mem_Union, simplify=None)

    Eq <<= Eq[-2].this.find(Element).apply(Set.Mem_Range.given.And), Eq[-1].this.find(Element).apply(Set.And.of.Mem_Range)

    Eq <<= Eq[-2].this.find(Element).apply(Set.Mem_Range.given.And), Eq[-1].this.find(Element).apply(Set.And.of.Mem_Range)




if __name__ == '__main__':
    run()
# created on 2022-01-08
