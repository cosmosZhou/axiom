from util import *


@apply
def apply(self, index=-1):
    a, b = self.of(Interval)
    kwargs = self.kwargs
    args = b.of(Min)
    former = Min(*args[:index])
    latter = Min(*args[index:])
    return Equal(self, Intersection(Interval(a, former, **kwargs), Interval(a, latter, **kwargs), evaluate=False))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    a, b, c = Symbol(integer=True)
    Eq << apply(Interval(a, Min(b, c), left_open=True))

    Eq << Sets.Eq.of.And.Imply.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(Sets.In_Interval.to.And), Eq[-1].this.rhs.apply(Sets.In_Interval.of.And)

    Eq <<= Eq[-2].this.find(LessEqual).apply(Algebra.Le_Min.to.And.Le), Eq[-1].this.find(LessEqual).apply(Algebra.Le_Min.of.And.Le)

    Eq <<= Eq[-2].this.find(Element).apply(Sets.In_Intersect.of.And, simplify=None), Eq[-1].this.find(Element).apply(Sets.In_Intersect.to.And, simplify=None)

    Eq <<= Eq[-2].this.find(Element).apply(Sets.In_Interval.of.And), Eq[-1].this.find(Element).apply(Sets.In_Interval.to.And)

    Eq <<= Eq[-2].this.find(Element).apply(Sets.In_Interval.of.And), Eq[-1].this.find(Element).apply(Sets.In_Interval.to.And)




if __name__ == '__main__':
    run()
# created on 2022-01-08
