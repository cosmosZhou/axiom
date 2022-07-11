from util import *


@apply
def apply(fx, interval, x=None):
    assert fx._subs(x, -x) == -fx
    return Equal(Inf[x:-interval](fx), -Sup[x:interval](fx))


@prove
def prove(Eq):
    from axiom import algebra

    m, M = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(x ** 3, Interval(m, M, right_open=True), x)

    f = Function(real=True)
    f[x] = x ** 3
    
    Eq << Equal(f(x), -f(-x), plausible=True)

    Eq << Eq[-1].this.lhs.defun()

    Eq << Eq[-1].this.find(f).defun()

    Eq << algebra.eq.imply.eq.sup_inf.st.odd_function.apply(Eq[-2], Eq[0].find(Interval), x)

    Eq << Eq[-1].this.find(f).defun()

    Eq << -Eq[-1].this.find(f).defun().reversed


if __name__ == '__main__':
    run()
# created on 2019-09-18
