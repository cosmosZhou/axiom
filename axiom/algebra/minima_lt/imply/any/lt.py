from util import *


@apply
def apply(given):
    (fx, *limits), M = given.of(Less[Minima])
    return Any(fx < M, *limits)


@prove
def prove(Eq):
    from axiom import algebra

    M, a, b = Symbol(real=True, given=True)
    x = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Minima[x:a:b](f(x)) < M)

    @Function
    def g(x):
        return -f(x)
    Eq.g_def = g(x).this.defun()

    Eq << -Eq.g_def.reversed

    Eq << Eq[0].subs(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(algebra.minima.to.neg.maxima)

    Eq << algebra.maxima_gt.imply.any.gt.apply(-Eq[-1])

    Eq << Eq[-1].subs(Eq.g_def)

    Eq << -Eq[-1].this.expr





if __name__ == '__main__':
    run()
# created on 2019-01-02
# updated on 2023-11-12
