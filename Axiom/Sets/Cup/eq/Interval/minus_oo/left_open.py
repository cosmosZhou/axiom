from util import *


@apply
def apply(self):
    interval, k = self.of(Cup[Tuple[0, oo]])
    _k1, _k = interval.of(Interval)
    assert _k1 == -k - 1 and _k == -k
    assert interval.left_open and not interval.right_open

    return Equal(self, Interval(-oo, 0))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    k = Symbol(integer=True)
    Eq << apply(Cup[k:oo](Interval(-k - 1, -k, left_open=True)))

    Eq << Sets.Eq.of.And.Imply.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(Sets.In_Cup.to.Any_In), Eq[-1].this.rhs.apply(Sets.In_Cup.of.Any_In)

    k = Eq[-1].rhs.variable
    x = Eq[-1].lhs.lhs
    Eq <<= Eq[-2].this.lhs.expr.apply(Sets.In_Interval.to.Ge), Eq[-1].this.rhs.apply(Algebra.Any.of.Cond.subs, k, -Ceiling(x))

    Eq <<= Eq[-2].this.lhs.apply(Algebra.Any.to.Any.And.limits.unleash, simplify=None), Algebra.Imply.of.And.Imply.apply(Eq[-1])

    Eq <<= Eq[-3].this.lhs.find(Element).apply(Sets.In_Range.to.Ge), Eq[-1].this.rhs.apply(Sets.In_Range.of.And), Algebra.Imply.of.Cond.apply(Eq[-2])

    Eq <<= Eq[-3].this.lhs.expr.apply(Algebra.Ge.Ge.to.Ge.Add), -Eq[-2].this.rhs, Sets.In_Interval.of.And.apply(Eq[-1])

    Eq << Eq[-4].this.lhs.apply(Sets.Le_0.to.is_nonpositive, simplify=None)

    Eq << Algebra.Gt_Sub_.Ceiling.One.apply(x)

    Eq << Eq[-3].this.lhs.apply(Sets.In_Interval.to.Le)

    Eq << Eq[-1].this.lhs.apply(Algebra.Le_0.to.Le_.Ceiling.Zero)

    Eq << Algebra.Le_Ceiling.apply(x)





if __name__ == '__main__':
    run()
# created on 2021-02-16
# updated on 2023-05-19
