from util import *


@apply
def apply(ge):
    x, a = ge.of(Greater)
    assert a > 0

    return Less(1 / x, 1 / a)


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(real=True)
    a = Symbol(real=True, positive=True)
    Eq << apply(x > a)

    Eq << Algebra.Gt.to.Gt_0.trans.apply(Eq[0])

    Eq << Algebra.Gt_0.to.Gt_0.Div.apply(Eq[-1])

    Eq << Algebra.Gt_0.Gt.to.Gt.Mul.apply(Eq[-1], Eq[0])

    Eq << Eq[1] * a


if __name__ == '__main__':
    run()
# created on 2019-07-28
