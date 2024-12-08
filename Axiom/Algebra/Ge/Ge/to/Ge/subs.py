from util import *


@apply
def apply(less_than_f, less_than):
    from Axiom.Algebra.Eq.Le.to.Le.subs import ratsimp
    assert less_than_f.is_GreaterEqual
    assert less_than.is_GreaterEqual

    lhs, rhs, k = ratsimp(less_than_f, less_than)
    assert k > 0
    return GreaterEqual(lhs, rhs)


@prove
def prove(Eq):
    from Axiom import Algebra
    y, b, x, t = Symbol(real=True)
    k = Symbol(real=True, positive=True)



    Eq << apply(y >= x * k + b, x >= t)

    Eq << Eq[1] * k + b

    Eq << Algebra.Ge.Ge.to.Ge.trans.apply(Eq[-1], Eq[0])

if __name__ == '__main__':
    run()
# created on 2019-05-18
