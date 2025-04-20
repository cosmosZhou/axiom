from util import *


@apply
def apply(less_than_f, less_than):
    from Axiom.Algebra.Le.of.Eq.Le.subs import ratsimp
    assert less_than_f.is_LessEqual
    assert less_than.is_LessEqual

    lhs, rhs, k = ratsimp(less_than_f, less_than)
    assert k > 0
    return LessEqual(lhs, rhs)


@prove
def prove(Eq):
    from Axiom import Algebra
    y, b, x, t = Symbol(real=True)
    k = Symbol(real=True, positive=True)

    Eq << apply(y <= x * k + b, x <= t)

    Eq << Eq[1] * k + b

    Eq << Algebra.Le.of.Le.Le.apply(Eq[-1], Eq[0])

if __name__ == '__main__':
    run()
# created on 2019-11-22
