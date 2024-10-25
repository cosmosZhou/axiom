from util import *


@apply
def apply(le, M=None):
    (fx, *limits), M0 = le.of(Sup < Expr)
    if M is None:
        M = le.generate_var(real=True, var='M')
    return Any[M:Interval.open(-oo, M0)](All(fx < M, *limits))


@prove
def prove(Eq):
    from axiom import algebra, sets

    M, M0, x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Sup[x:Interval(a, b, left_open=True, right_open=True)](f(x)) < M0, M)

    y = Symbol(Eq[0].lhs)
    Eq << y.this.definition

    Eq <<= algebra.eq_sup.then.all.le.apply(Eq[-1]), Eq[0].subs(Eq[-1].reversed), algebra.any.of.cond.subs.apply(Eq[1], M, (y + M0) / 2)

    Eq.all, *Eq[-2:] = algebra.cond.all.then.all.et.apply(Eq[-2], Eq[-3], simplify=None), algebra.et.of.et.apply(Eq[-1])

    Eq << sets.el.of.el.mul.interval.apply(Eq[-2], 2)

    Eq << sets.el.of.el.sub.apply(Eq[-1], M0)

    Eq << sets.el_interval.of.et.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[2])

    Eq << algebra.then.all.sup_ge.apply(Eq[-1].lhs)

    Eq << algebra.all.then.cond.subs.apply(Eq[-1], x, (a + b) / 2)

    Eq << algebra.ge.then.gt.relax.apply(Eq[-1], -oo)

    Eq << Eq.all.this.expr.apply(algebra.lt.le.then.lt.trans, ret=1)

    Eq << Eq[-1].this.expr.apply(algebra.lt.le.then.lt.add)

    Eq << Eq[-1].this.expr / 2





if __name__ == '__main__':
    run()
# created on 2018-12-28
# updated on 2023-05-20
