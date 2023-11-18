from util import *


@apply
def apply(le, M=None):
    (fx, *limits), M0 = le.of(Inf > Expr)
    if M is None:
        M = le.generate_var(real=True, var='M')
    return Any[M:Interval.open(M0, oo)](All(fx > M, *limits))


@prove
def prove(Eq):
    from axiom import algebra, sets

    M, M0, x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Inf[x:Interval(a, b, left_open=True, right_open=True)](f(x)) > M0, M)

    y = Symbol(Eq[0].lhs)
    Eq << y.this.definition

    Eq <<= algebra.eq_inf.imply.all.ge.apply(Eq[-1]), Eq[0].subs(Eq[-1].reversed), algebra.any.given.cond.subs.apply(Eq[1], M, (y + M0) / 2)

    Eq.all, *Eq[-2:] = algebra.cond.all.imply.all.et.apply(Eq[-2], Eq[-3], simplify=None), algebra.et.given.et.apply(Eq[-1])

    Eq << sets.el.given.el.mul.interval.apply(Eq[-2], 2)

    Eq << sets.el.given.el.sub.apply(Eq[-1], M0)

    Eq << sets.el_interval.given.et.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[2])

    Eq << algebra.imply.all.inf_le.apply(Eq[-1].lhs)

    Eq << algebra.all.imply.cond.subs.apply(Eq[-1], x, (a + b) / 2)

    Eq << algebra.le.imply.lt.relax.apply(Eq[-1], oo)

    Eq << Eq.all.this.expr.apply(algebra.gt.ge.imply.gt.transit, ret=1)

    Eq << Eq[-1].this.expr.apply(algebra.gt.ge.imply.gt.add)

    Eq << Eq[-1].this.expr / 2





if __name__ == '__main__':
    run()
# created on 2019-01-05
# updated on 2023-05-19
