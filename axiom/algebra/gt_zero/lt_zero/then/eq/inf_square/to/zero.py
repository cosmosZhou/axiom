from util import *


@apply
def apply(is_positive, is_negative, left_open=True, right_open=True, x=None):
    M = is_positive.of(Expr > 0)
    m = is_negative.of(Expr < 0)
    if x is None:
        x = m.generate_var(M.free_symbols, real=True)

    self = Inf[x:Interval(m, M, left_open=left_open, right_open=right_open)](x ** 2)
    return Equal(self, 0)


@prove
def prove(Eq):
    from axiom import sets, algebra

    m, M = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(M > 0, m < 0, x=x)

    Eq << sets.gt.lt.then.el.interval.apply(Eq[0], Eq[1])
    Eq << algebra.eq.of.et.squeeze.apply(Eq[2])

    t = Symbol(real=True)
    Eq <<= algebra.inf_le.of.all_any_lt.apply(Eq[-2], t), algebra.inf_ge.of.all.ge.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(algebra.any.of.cond.subs, x, 0)

    Eq << Eq[-1].this.args[1].apply(algebra.all.to.ou)


if __name__ == '__main__':
    run()
# created on 2019-08-24
