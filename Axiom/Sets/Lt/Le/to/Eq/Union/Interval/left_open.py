from util import *


@apply
def apply(lt, le, right_open=False, left_open=False):
    a, x = lt.of(Less)
    S[x], b = le.of(LessEqual)
    return Equal(Interval(a, x, left_open=left_open) | Interval(x, b, left_open=True, right_open=right_open), Interval(a, b, left_open=left_open, right_open=right_open))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    a, b, x = Symbol(real=True, given=True)
    Eq << apply(a < x, x <= b)

    Eq << Sets.Eq.of.And.Imply.apply(Eq[2])

    Eq <<= Eq[-2].this.lhs.apply(Sets.In_Union.to.Or), Eq[-1].this.rhs.apply(Sets.In_Union.of.Or)

    Eq <<= Algebra.Imply_Or.of.And.Imply.apply(Eq[-2]), Eq[-1].this.apply(Algebra.Imply.contraposition)

    Eq <<= Eq[-3].this.lhs.apply(Sets.In_Interval.to.And), Eq[-2].this.lhs.apply(Sets.In_Interval.to.And), Eq[-1].this.lhs.args[0].apply(Sets.NotIn_Interval.to.Or)

    Eq <<= Eq[-3].this.rhs.apply(Sets.In_Interval.of.And), Eq[-2].this.rhs.apply(Sets.In_Interval.of.And), Eq[-1].this.lhs.find(NotElement).apply(Sets.NotIn_Interval.to.Or)

    Eq <<= Algebra.Cond.to.Imply.And.apply(Eq[0], cond=Eq[-3].lhs), Algebra.Cond.to.Imply.And.apply(Eq[1], cond=Eq[-2].lhs), Eq[-1].this.rhs.apply(Sets.NotIn_Interval.of.Or)

    Eq <<= Eq[-3].this.rhs.args[:2].apply(Algebra.Lt.Gt.to.Ge.relax), Eq[-2].this.rhs.args[:2].apply(Algebra.Le.Le.to.Le.trans),  Eq[-1].this.lhs.apply(Algebra.And.to.Or)

    Eq << Algebra.Imply_Or.of.And.Imply.apply(Eq[-1])

    Eq << Algebra.Imply.of.Imply.split.And.apply(Eq[-2])

    Eq << Algebra.Imply.of.Imply.split.And.apply(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2018-10-13
# updated on 2023-05-12
