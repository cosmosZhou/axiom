from util import *


@apply
def apply(lt_zero, le, x):
    λ = lt_zero.of(Expr < 0)
    a, b = le.of(LessEqual)
    return Equal(clip(λ * x, λ * b, λ * a), λ * clip(x, a, b))


@prove
def prove(Eq):
    from Axiom import Algebra

    x, a, b = Symbol(real=True)
    λ = Symbol(real=True)
    Eq << apply(λ < 0, a <= b, x)

    Eq << Eq[-1].this.find(clip).defun()

    Eq << Algebra.Lt_0.to.Min.eq.Mul.Max.apply(Eq[0], Eq[3].lhs)

    Eq << Algebra.Lt_0.to.Max.eq.Mul.Min.apply(Eq[0], Eq[-1].rhs.find(Mul[~Max]))

    Eq << Eq[-2].this.rhs.subs(Eq[-1])

    Eq << Eq[-4].subs(Eq[-1])

    Eq << Algebra.Le.to.Clip.eq.Max.apply(Eq[1], x)

    Eq << Eq[-2].this.subs(Eq[-1])



if __name__ == '__main__':
    run()
# created on 2023-03-26
