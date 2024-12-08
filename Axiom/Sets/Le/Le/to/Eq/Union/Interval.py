from util import *


@apply
def apply(le, _le, right_open=True, left_open=None):
    x, a = le.of(LessEqual)
    b, _x = _le.of(LessEqual)
    if x != _x:
        a, x, S[x], b = _x, b, a, x,
    if left_open is not None:
        right_open = not left_open
    return Equal(Interval(b, x, right_open=right_open) | Interval(x, a, left_open=not right_open), Interval(b, a))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    a, b, x = Symbol(real=True, given=True)
    Eq << apply(x <= b, a <= x)

    Eq << Sets.Eq.of.And.Imply.apply(Eq[2])

    Eq <<= Eq[-2].this.lhs.apply(Sets.In_Union.to.Or), Eq[-1].this.rhs.apply(Sets.In_Union.of.Or)

    Eq <<= Algebra.Imply_Or.of.And.Imply.apply(Eq[-2]), Eq[-1].this.apply(Algebra.Imply.contraposition)

    Eq <<= Eq[-3].this.lhs.apply(Sets.In_Interval.to.And), Eq[-2].this.lhs.apply(Sets.In_Interval.to.And), Eq[-1].this.lhs.args[0].apply(Sets.NotIn_Interval.to.Or)

    Eq <<= Eq[-3].this.rhs.apply(Sets.In_Interval.of.And), Eq[-2].this.rhs.apply(Sets.In_Interval.of.And), Eq[-1].this.lhs.find(NotElement).apply(Sets.NotIn_Interval.to.Or)

    Eq <<= Algebra.Cond.to.Imply.And.apply(Eq[0], cond=Eq[-3].lhs), Algebra.Cond.to.Imply.And.apply(Eq[1], cond=Eq[-2].lhs), Eq[-1].this.rhs.apply(Sets.NotIn_Interval.of.Or)

    Eq <<= Eq[-3].this.rhs.args[:2].apply(Algebra.Le.Lt.to.Le.relax), Eq[-2].this.rhs.args[::2].apply(Algebra.Le.Ge.to.Ge.trans),  Eq[-1].this.lhs.apply(Algebra.And.to.Or)

    Eq << Algebra.Imply_Or.of.And.Imply.apply(Eq[-1])

    Eq << Algebra.Imply.of.Imply.split.And.apply(Eq[-2])

    Eq << Algebra.Imply.of.Imply.split.And.apply(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2021-05-23
# updated on 2023-05-12

