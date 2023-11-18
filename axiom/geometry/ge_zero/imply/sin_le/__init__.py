from util import *


@apply
def apply(gt_zero):
    x = gt_zero.of(Expr >= 0)
    return sin(x) <= x

@prove
def prove(Eq):
    from axiom import calculus, geometry, sets, algebra

    x = Symbol(real=True)
    Eq << apply(x >= 0)

    @Function(real=True)
    def f(x):
        return x - sin(x)
    Eq << f(x).this.defun()

    Eq << calculus.eq.imply.eq.grad.apply(Eq[-1], (x,))

    Eq << Eq[-1].this.rhs.apply(calculus.grad.to.add)

    Eq << geometry.imply.el.cos.apply(x)

    Eq << sets.el_interval.imply.le.apply(Eq[-1])

    Eq << algebra.le.imply.ge_zero.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[-4].reversed)

    Eq << algebra.cond.imply.all.restrict.apply(Eq[-1], (x, Interval(0, oo)))

    Eq << calculus.all_ge_zero.imply.all.ge.monotony.right_open.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[2])

    Eq << Eq[-1].this.find(f).defun()

    Eq << algebra.all.imply.infer.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.ge_zero.imply.le)

    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[0], Eq[-1])



if __name__ == '__main__':
    run()
# created on 2023-10-03

from . import quadratic