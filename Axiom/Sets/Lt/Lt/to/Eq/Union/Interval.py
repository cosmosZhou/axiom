from util import *


@apply
def apply(lt_a, lt_b, right_open=True, left_open=None):
    a, x = lt_a.of(Less)
    S[x], b = lt_b.of(LessEqual)
    if left_open is not None:
        right_open = not left_open
    return Equal(Interval(a, x, left_open=True, right_open=right_open) | Interval(x, b, left_open=not right_open, right_open=True), Interval(a, b, left_open=True, right_open=True))


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

    Eq <<= Algebra.Cond.to.Imply.And.apply(Eq[1], cond=Eq[-3].lhs), Algebra.Cond.to.Imply.And.apply(Eq[0], cond=Eq[-2].lhs), Eq[-1].this.rhs.apply(Sets.NotIn_Interval.of.Or)

    Eq <<= Eq[-3].this.rhs.args[::2].apply(Algebra.Le.Lt.to.Lt.trans), Eq[-2].this.rhs.args[::2].apply(Algebra.Lt.Ge.to.Gt.trans),  Eq[-1].this.lhs.apply(Algebra.And.to.Or)

    Eq << Algebra.Imply_Or.of.And.Imply.apply(Eq[-1])

    Eq << Algebra.Imply.of.Imply.split.And.apply(Eq[-2], 1)

    Eq << Algebra.Imply.of.Imply.split.And.apply(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2021-06-02
# updated on 2023-05-20
