from util import *


@apply
def apply(eq_grad):
    (fx, (x, S[1])), y = eq_grad.of(Equal[Derivative])
    return Equal(Derivative[x + S.Infinitesimal](fx), y), Equal(Derivative[x - S.Infinitesimal](fx), y)


@prove
def prove(Eq):
    from axiom import calculus

    x, y = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Equal(Derivative[x](f(x)), y))

    Eq << Eq[0].this.lhs.apply(calculus.grad.to.limit)

    Eq << calculus.eq_limit.imply.et.eq_limit.apply(Eq[-1])

    Eq << Eq[1].this.lhs.apply(calculus.grad.to.limit.one_sided)

    Eq << Eq[2].this.lhs.apply(calculus.grad.to.limit.one_sided)


if __name__ == '__main__':
    run()
# created on 2023-11-10
