from util import *


@apply
def apply(le_zero):
    x = le_zero.of(Expr >= 0)
    return sin(x) <= x * (1 + x / S.Pi)

@prove
def prove(Eq):
    from axiom import calculus, geometry, sets, algebra

    x = Symbol(real=True)
    Eq << apply(x >= 0)

    @Function
    def f(x):
        return x * (1 + x / S.Pi) - sin(x)
    Eq << f(x).this.defun()

    Eq << calculus.eq.imply.eq.grad.apply(Eq[-1], (x,))

    Eq.eq_grad = Eq[-1].this.rhs.apply(calculus.grad.to.add)

    Eq << geometry.imply.el.cos.apply(x)

    Eq << -sets.el_interval.imply.le.apply(Eq[-1])

    Eq << Eq[-1] + 1

    Eq << Eq[0] * 2 / S.Pi

    Eq << Eq[-1] + Eq[-2]

    Eq << algebra.eq.ge.imply.ge.transit.apply(Eq.eq_grad, Eq[-1])

    Eq << algebra.cond.imply.all.restrict.apply(Eq[-1], (x, Interval(0, oo)))

    Eq << calculus.all_ge_zero.imply.all.ge.monotony.right_open.apply(Eq[-1])

    Eq << Eq[-1].this.find(f).defun()

    Eq << Eq[-1].this.find(f).defun()

    Eq << algebra.all.imply.infer.apply(Eq[-1])

    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[0], Eq[-1])

    Eq << algebra.ge_zero.imply.le.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-10-03