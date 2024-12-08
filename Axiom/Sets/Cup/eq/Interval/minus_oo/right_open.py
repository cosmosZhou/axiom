from util import *


@apply
def apply(self):
    interval, k = self.of(Cup[Tuple[0, oo]])
    _k1, _k = interval.of(Interval)
    assert _k1 == -k - 1 and _k == -k
    assert not interval.left_open and interval.right_open

    return Equal(self, Interval.open(-oo, 0))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    k = Symbol(integer=True)
    Eq << apply(Cup[k:oo](Interval(-k - 1, -k, right_open=True)))

    Eq << Sets.Eq.of.And.Imply.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(Sets.In_Cup.to.Any_In), Eq[-1].this.rhs.apply(Sets.In_Cup.of.Any_In)

    k = Eq[-1].rhs.variable
    x = Eq[-1].lhs.lhs
    Eq <<= Eq[-2].this.lhs.expr.apply(Sets.In_Interval.to.Lt), Eq[-1].this.rhs.apply(Algebra.Any.of.Cond.subs, k, -Floor(x) - 1)

    Eq <<= Eq[-2].this.lhs.apply(Algebra.Any.to.Any.And.limits.unleash, simplify=None), Algebra.Imply.of.And.Imply.apply(Eq[-1])

    Eq <<= Eq[-3].this.lhs.find(Element).apply(Sets.In_Range.to.Le), Eq[-1].this.rhs.apply(Sets.In_Range.of.And), Algebra.Imply.of.Cond.apply(Eq[-2])

    Eq <<= Eq[-3].this.lhs.expr.apply(Algebra.Le.Lt.to.Lt.Add), Eq[-2].this.rhs.apply(Algebra.Ge.transport, lhs=0), Sets.In_Interval.of.And.apply(Eq[-1])

    Eq << Eq[-4].this.lhs.apply(Sets.Lt_0.to.is_negative, simplify=None)

    Eq << Algebra.Ge_Floor.apply(x)

    Eq << Algebra.Lt_Add_.Floor.One.apply(x)

    Eq << -Eq[-3].this.rhs

    Eq << Eq[-1].this.rhs.apply(Algebra.Le.of.Lt.One)

    Eq << Eq[-1].this.lhs.apply(Sets.In_Interval.to.Lt)

    Eq << Eq[-1].this.lhs.apply(Algebra.Lt_0.to.Lt_.Floor.Zero)



if __name__ == '__main__':
    run()
# created on 2021-02-17
# updated on 2023-05-14
