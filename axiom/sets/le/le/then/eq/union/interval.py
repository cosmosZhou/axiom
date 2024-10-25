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
    from axiom import sets, algebra

    a, b, x = Symbol(real=True, given=True)
    Eq << apply(x <= b, a <= x)

    Eq << sets.eq.of.et.infer.apply(Eq[2])

    Eq <<= Eq[-2].this.lhs.apply(sets.el_union.then.ou), Eq[-1].this.rhs.apply(sets.el_union.of.ou)

    Eq <<= algebra.infer_ou.of.et.infer.apply(Eq[-2]), Eq[-1].this.apply(algebra.infer.contraposition)

    Eq <<= Eq[-3].this.lhs.apply(sets.el_interval.then.et), Eq[-2].this.lhs.apply(sets.el_interval.then.et), Eq[-1].this.lhs.args[0].apply(sets.notin_interval.then.ou)

    Eq <<= Eq[-3].this.rhs.apply(sets.el_interval.of.et), Eq[-2].this.rhs.apply(sets.el_interval.of.et), Eq[-1].this.lhs.find(NotElement).apply(sets.notin_interval.then.ou)

    Eq <<= algebra.cond.then.infer.et.apply(Eq[0], cond=Eq[-3].lhs), algebra.cond.then.infer.et.apply(Eq[1], cond=Eq[-2].lhs), Eq[-1].this.rhs.apply(sets.notin_interval.of.ou)

    Eq <<= Eq[-3].this.rhs.args[:2].apply(algebra.le.lt.then.le.relax), Eq[-2].this.rhs.args[::2].apply(algebra.le.ge.then.ge.trans),  Eq[-1].this.lhs.apply(algebra.et.then.ou)

    Eq << algebra.infer_ou.of.et.infer.apply(Eq[-1])

    Eq << algebra.infer.of.infer.split.et.apply(Eq[-2])

    Eq << algebra.infer.of.infer.split.et.apply(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2021-05-23
# updated on 2023-05-12
