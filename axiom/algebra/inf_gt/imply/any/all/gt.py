from util import *


@apply
def apply(le, M=None):
    (fx, *limits), M0 = le.of(Inf > Expr)
    if M is None:
        M = le.generate_var(real=True, var='M')
    return Any[M:Interval.open(M0, oo)](All(fx > M, *limits))


@prove
def prove(Eq):
    from axiom import algebra

    M, M0, x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Inf[x:Interval(a, b, left_open=True, right_open=True)](f(x)) > M0, M)

    @Function
    def g(x):
        return -f(x)
    Eq << g(x).this.defun().reversed

    Eq << Eq[0].subs(-Eq[-1])

    Eq << Eq[-1].this.lhs.apply(algebra.inf.to.neg.sup)

    Eq << -Eq[-1]

    Eq << algebra.sup_lt.imply.any.all.lt.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[2].reversed)

    Eq << -Eq[-1].this.find(Less)

    Eq << algebra.any.imply.any.limits.negate.apply(Eq[-1])

    


if __name__ == '__main__':
    run()
# created on 2019-01-05
# updated on 2024-06-27
