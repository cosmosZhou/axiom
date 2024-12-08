from util import *


@apply
def apply(self, index=-1):
    a, b = self.of(Interval)
    kwargs = self.kwargs
    args = b.of(Max)
    former = Max(*args[:index])
    latter = Max(*args[index:])
    return Equal(self, Union(Interval(a, former, **kwargs), Interval(a, latter, **kwargs), evaluate=False))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    a, b, c = Symbol(integer=True)
    Eq << apply(Interval(a, Max(b, c), left_open=True, right_open=True))

    Eq << Sets.Eq.of.And.Imply.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(Sets.In_Interval.to.And), Eq[-1].this.rhs.apply(Sets.In_Interval.of.And)

    Eq <<= Eq[-2].this.find(Less).apply(Algebra.Lt_Max.to.Or.Lt), Eq[-1].this.find(Less).apply(Algebra.Lt_Max.of.Or.Lt)

    Eq <<= Eq[-2].this.find(Element).apply(Sets.In_Union.of.Or, simplify=None), Eq[-1].this.find(Element).apply(Sets.In_Union.to.Or, simplify=None)

    Eq <<= Eq[-2].this.find(Element).apply(Sets.In_Interval.of.And), Eq[-1].this.find(Element).apply(Sets.In_Interval.to.And)

    Eq <<= Eq[-2].this.find(Element).apply(Sets.In_Interval.of.And), Eq[-1].this.find(Element).apply(Sets.In_Interval.to.And)




if __name__ == '__main__':
    run()
# created on 2022-01-08
