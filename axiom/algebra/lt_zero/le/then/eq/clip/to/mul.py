from util import *


@apply
def apply(lt_zero, le, x):
    λ = lt_zero.of(Expr < 0)
    a, b = le.of(LessEqual)
    return Equal(clip(λ * x, λ * b, λ * a), λ * clip(x, a, b))


@prove
def prove(Eq):
    from axiom import algebra

    x, a, b = Symbol(real=True)
    λ = Symbol(real=True)
    Eq << apply(λ < 0, a <= b, x)

    Eq << Eq[-1].this.find(clip).defun()

    Eq << algebra.lt_zero.then.eq.min.to.mul.max.apply(Eq[0], Eq[3].lhs)

    Eq << algebra.lt_zero.then.eq.max.to.mul.min.apply(Eq[0], Eq[-1].rhs.find(Mul[~Max]))

    Eq << Eq[-2].this.rhs.subs(Eq[-1])

    Eq << Eq[-4].subs(Eq[-1])

    Eq << algebra.le.then.eq.clip.to.max.apply(Eq[1], x)

    Eq << Eq[-2].this.subs(Eq[-1])



if __name__ == '__main__':
    run()
# created on 2023-03-26
