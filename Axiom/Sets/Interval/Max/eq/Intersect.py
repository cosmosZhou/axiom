from util import *


@apply
def apply(self, index=-1):
    a, b = self.of(Interval)
    kwargs = self.kwargs
    args = a.of(Max)
    former = Max(*args[:index])
    latter = Max(*args[index:])
    return Equal(self, Intersection(Interval(former, b, **kwargs), Interval(latter, b, **kwargs), evaluate=False))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    a, b, c = Symbol(integer=True)
    Eq << apply(Interval(Max(b, c), a))

    Eq << Sets.Eq.of.And.Imply.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(Sets.In_Interval.to.And), Eq[-1].this.rhs.apply(Sets.In_Interval.of.And)

    Eq <<= Eq[-2].this.find(GreaterEqual).apply(Algebra.Ge_Max.to.And.Ge), Eq[-1].this.find(GreaterEqual).apply(Algebra.Ge_Max.of.And.Ge)

    Eq <<= Eq[-2].this.find(Element).apply(Sets.In_Intersect.of.And, simplify=None), Eq[-1].this.find(Element).apply(Sets.In_Intersect.to.And, simplify=None)

    Eq <<= Eq[-2].this.find(Element).apply(Sets.In_Interval.of.And), Eq[-1].this.find(Element).apply(Sets.In_Interval.to.And)

    Eq <<= Eq[-2].this.find(Element).apply(Sets.In_Interval.of.And), Eq[-1].this.find(Element).apply(Sets.In_Interval.to.And)




if __name__ == '__main__':
    run()
# created on 2022-01-08
