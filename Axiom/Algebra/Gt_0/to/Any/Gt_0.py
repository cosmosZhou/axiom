from util import *


@apply
def apply(gt_zero, x=None, b=None):
    a = gt_zero.of(Expr > 0)
    assert x.is_real
    assert a.is_real and b.is_real
    return Any[x](a * x + b > 0)


@prove
def prove(Eq):
    from Axiom import Algebra

    a, b = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(a > 0, x=x, b=b)

    Eq << Algebra.Gt_0.to.Gt_0.Div.apply(Eq[0])

    epsilon = Symbol(negative=True)
    Eq << Algebra.Any.of.Cond.subs.apply(Eq[1], x, Eq[2].lhs * -b - epsilon)

    Eq << Eq[-1].this.find(Mul).apply(Algebra.Mul.eq.Add)

    Eq << -Eq[0] * epsilon




if __name__ == '__main__':
    run()
# created on 2022-04-03