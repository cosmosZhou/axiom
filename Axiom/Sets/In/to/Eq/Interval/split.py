from util import *


@apply
def apply(given, right_open=True):
    x, interval = given.of(Element)
    a, b = interval.of(Interval)
    return Equal(interval, Interval(a, x, left_open=interval.left_open, right_open=right_open) | Interval(x, b, left_open=not right_open, right_open=interval.right_open))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x, a, b, t = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b, left_open=True)), right_open=False)

    Eq << Sets.Eq.of.And.Imply.apply(Eq[1], t)

    Eq <<= Eq[-2].this.rhs.apply(Sets.In_Union.of.Or), Eq[-1].this.lhs.apply(Sets.In_Union.to.Or)

    Eq <<= Eq[-2].this.lhs.apply(Sets.In_Interval.to.And), Eq[-1].this.rhs.apply(Sets.In_Interval.of.And)

    Eq <<= Eq[-2].this.find(Element).apply(Sets.In_Interval.of.And), Eq[-1].this.find(Element).apply(Sets.In_Interval.to.And)

    Eq <<= Eq[-2].this.find(Element).apply(Sets.In_Interval.of.And), Eq[-1].this.find(Element).apply(Sets.In_Interval.to.And)

    Eq << Algebra.Imply_Or.of.And.Imply.apply(Eq[-1])

    Eq <<= Algebra.Imply.of.Imply.split.And.apply(Eq[-2], 1), Algebra.Imply.of.Imply.split.And.apply(Eq[-1], 0)

    Eq << Sets.In_Interval.to.And.apply(Eq[0])

    Eq <<= Algebra.Cond.to.Imply.apply(Eq[-2], cond=t > x), Algebra.Cond.to.Imply.apply(Eq[-1], cond=t <= x)

    Eq <<= Algebra.Imply_And.to.Imply.And.apply(Eq[-2]), Algebra.Imply_And.to.Imply.And.apply(Eq[-1])

    Eq <<= Eq[-2].this.rhs.apply(Algebra.Gt.Gt.to.Gt.trans), Eq[-1].this.rhs.apply(Algebra.Le.Le.to.Le.trans)


if __name__ == '__main__':
    run()
# created on 2020-11-22
