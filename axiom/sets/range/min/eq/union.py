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
    from Axiom import Sets, Algebra

    a, b, c = Symbol(integer=True)
    Eq << apply(Range(Min(b, c), a))

    Eq << Sets.Eq.of.And.Imply.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(Sets.In_Range.to.And), Eq[-1].this.rhs.apply(Sets.In_Range.of.And)

    Eq <<= Eq[-2].this.find(GreaterEqual).apply(Algebra.Ge_Min.to.Or.Ge), Eq[-1].this.find(GreaterEqual).apply(Algebra.Ge_Min.of.Or.Ge)

    Eq <<= Eq[-2].this.find(Element).apply(Sets.In_Union.of.Or, simplify=None), Eq[-1].this.find(Element).apply(Sets.In_Union.to.Or, simplify=None)

    Eq <<= Eq[-2].this.find(Element).apply(Sets.In_Range.of.And), Eq[-1].this.find(Element).apply(Sets.In_Range.to.And)

    Eq <<= Eq[-2].this.find(Element).apply(Sets.In_Range.of.And), Eq[-1].this.find(Element).apply(Sets.In_Range.to.And)




if __name__ == '__main__':
    run()
# created on 2022-01-08
