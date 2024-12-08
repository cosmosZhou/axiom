from util import *


@apply
def apply(gt_zero):
    x = gt_zero.of(Expr >= 0)
    return sin(x) <= x

@prove
def prove(Eq):
    from Axiom import Calculus, Geometry, Sets, Algebra

    x = Symbol(real=True)
    Eq << apply(x >= 0)

    @Function(real=True)
    def f(x):
        return x - sin(x)
    Eq << f(x).this.defun()

    Eq << Calculus.Eq.to.Eq.Grad.apply(Eq[-1], (x,))

    Eq << Eq[-1].this.rhs.apply(Calculus.Grad.eq.Add)

    Eq << Geometry.Cos.el.Interval.apply(x)

    Eq << Sets.In_Interval.to.Le.apply(Eq[-1])

    Eq << Algebra.Le.to.Ge_0.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[-4].reversed)

    Eq << Algebra.Cond.to.All.restrict.apply(Eq[-1], (x, Interval(0, oo)))

    Eq << Calculus.All_Ge_0.to.All.Ge.monotony.right_open.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[2])

    Eq << Eq[-1].this.find(f).defun()

    Eq << Algebra.All.to.Imply.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Ge_0.to.Le)

    Eq << Algebra.Cond.Imply.to.Cond.trans.apply(Eq[0], Eq[-1])



if __name__ == '__main__':
    run()
# created on 2023-10-03

from . import quadratic
