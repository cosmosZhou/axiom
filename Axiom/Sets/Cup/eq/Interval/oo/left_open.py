from util import *


@apply
def apply(self):
    interval, k = self.of(Cup[Tuple[0, oo]])
    S[k], S[k + 1] = interval.of(Interval)
    assert interval.left_open and not interval.right_open

    return Equal(self, Interval.open(0, oo))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    k = Symbol(integer=True)
    Eq << apply(Cup[k:oo](Interval(k, k + 1, left_open=True)))

    Eq << Sets.Eq.of.And.Imply.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(Sets.In_Cup.to.Any_In), Eq[-1].this.rhs.apply(Sets.In_Cup.of.Any_In)

    k = Eq[-1].rhs.variable
    x = Eq[-1].lhs.lhs
    Eq <<= Eq[-2].this.lhs.expr.apply(Sets.In_Interval.to.Gt), Eq[-1].this.rhs.apply(Algebra.Any.of.Cond.subs, k, Ceiling(x) - 1)

    Eq <<= Eq[-2].this.lhs.apply(Algebra.Any.to.Any.And.limits.unleash, simplify=None), Algebra.Imply.of.And.Imply.apply(Eq[-1])

    Eq <<= Eq[-3].this.lhs.find(Element).apply(Sets.In_Range.to.Ge), Algebra.Imply.of.Cond.apply(Eq[-2]), Eq[-1].this.rhs.apply(Sets.In_Range.of.And)

    Eq <<= Eq[-3].this.lhs.expr.apply(Algebra.Gt.Ge.to.Gt.trans), Sets.In_Interval.of.And.apply(Eq[-2]), Eq[-1].this.rhs.apply(Algebra.Ge.transport, lhs=0)

    Eq << Eq[-4].this.lhs.apply(Sets.Gt_0.to.is_positive, simplify=None)

    Eq << Algebra.Gt_Sub_.Ceiling.One.apply(x)

    Eq << Algebra.Le_Ceiling.apply(x)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Eq[-1].this.lhs.apply(Algebra.Gt_0.to.Gt_0.Ceiling)

    Eq << Eq[-1].this.lhs.apply(Algebra.Gt.to.Ge.strengthen)




if __name__ == '__main__':
    run()
# created on 2021-02-13
# updated on 2023-05-12
