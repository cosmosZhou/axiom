from util import *


@apply
def apply(le, M=None):
    (fx, *limits), M0 = le.of(Sup < Expr)
    if M is None:
        M = le.generate_var(real=True, var='M')
    return Any[M:Interval(-oo, M0, right_open=True)](All(fx < M, *limits))


@prove
def prove(Eq):
    from axiom import algebra

    M, M0, x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Sup[x:Interval(a, b, left_open=True, right_open=True)](f(x)) < M0, M)

    y = Symbol(Eq[0].lhs)
    Eq << y.this.definition

    Eq <<= algebra.eq_sup.imply.all_le.apply(Eq[-1]), Eq[0].subs(Eq[-1].reversed), algebra.any.given.cond.subs.apply(Eq[1], M, (y + M0) / 2)

    Eq <<= algebra.cond.all.imply.all_et.apply(Eq[-2], Eq[-3], simplify=None), algebra.et.given.et.apply(Eq[-1])

    Eq << Eq[-2] * 2 - M0

    Eq << Eq[-3].this.expr.apply(algebra.lt.le.imply.lt.transit, ret=0)

    Eq << Eq[-1].this.expr.apply(algebra.lt.le.imply.lt.add)
    Eq << Eq[-1].this.expr / 2


if __name__ == '__main__':
    run()
# created on 2018-12-28
