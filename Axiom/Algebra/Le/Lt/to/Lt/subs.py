from util import *


@apply
def apply(less_than_f, less_than):
    from Axiom.Algebra.Eq.Le.to.Le.subs import ratsimp
    if not less_than_f.is_LessEqual:
        less_than, less_than_f = given

    assert less_than_f.is_LessEqual
    assert less_than.is_Less

    lhs, rhs, k = ratsimp(less_than_f, less_than)
    assert k > 0
    return Less(lhs, rhs)


@prove
def prove(Eq):
    from Axiom import Algebra
    y, b, x, t = Symbol(real=True)
    k = Symbol(real=True, positive=True)

    Eq << apply(y <= x * k + b, x < t)

    Eq << Eq[1] * k + b

    Eq << Algebra.Le.Lt.to.Lt.trans.apply(Eq[-1], Eq[0])

if __name__ == '__main__':
    run()
# created on 2019-11-25