from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Greater)

    return Greater(exp(lhs), exp(rhs))


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y = Symbol(real=True)
    Eq << apply(Greater(x, y))

    Eq << Algebra.Lt.to.Lt.Exp.apply(Eq[0].reversed).reversed


if __name__ == '__main__':
    run()
# created on 2023-04-16