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
    from Axiom import Sets, Algebra

    a, b, c = Symbol(integer=True)
    Eq << apply(Range(a, Min(b, c)))

    Eq << Sets.Eq.of.And.Imply.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(Sets.In_Range.to.And), Eq[-1].this.rhs.apply(Sets.In_Range.of.And)

    Eq <<= Eq[-2].this.find(Less).apply(Algebra.Lt_Min.to.And.Lt), Eq[-1].this.find(Less).apply(Algebra.Lt_Min.of.And.Lt)

    Eq <<= Eq[-2].this.find(Element).apply(Sets.In_Intersect.of.And, simplify=None), Eq[-1].this.find(Element).apply(Sets.In_Intersect.to.And, simplify=None)

    Eq <<= Eq[-2].this.find(Element).apply(Sets.In_Range.of.And), Eq[-1].this.find(Element).apply(Sets.In_Range.to.And)

    Eq <<= Eq[-2].this.find(Element).apply(Sets.In_Range.of.And), Eq[-1].this.find(Element).apply(Sets.In_Range.to.And)




if __name__ == '__main__':
    run()
# created on 2022-01-01

