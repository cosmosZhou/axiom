from util import *


@apply
def apply(given):
    x = given.of(Expr > 0)
    return Greater(abs(x), 0)


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(real=True, given=True)
    Eq << apply(Greater(x, 0))

    Eq << Algebra.Gt_0.to.Eq.Abs.apply(Eq[0])

    Eq << Eq[0].subs(Eq[-1].reversed)








if __name__ == '__main__':
    run()
# created on 2019-08-11
