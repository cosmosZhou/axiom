from util import *


@apply
def apply(le, M=None):
    (fx, *limits), M0 = le.of(Sup < Expr)
    if M is None:
        M = le.generate_var(real=True, var='M')
    return Any[M:Interval.open(-oo, M0)](All(fx <= M, *limits))


@prove
def prove(Eq):
    from axiom import algebra

    M, M0, x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Sup[x:Interval(a, b, left_open=True, right_open=True)](f(x)) < M0, M)

    Eq << algebra.sup_lt.imply.any.all.lt.apply(Eq[0])
    Eq << Eq[-1].this.expr.expr.apply(algebra.lt.imply.le.relax)


if __name__ == '__main__':
    run()
# created on 2018-12-29
