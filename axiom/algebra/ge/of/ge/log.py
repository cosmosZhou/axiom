from util import *


@apply
def apply(ge):
    lhs, rhs = ge.of(GreaterEqual)
    return log(lhs) >= log(rhs)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(GreaterEqual(x, y))

    Eq << Algebra.Ge.to.Ge.Exp.apply(Eq[1])


if __name__ == '__main__':
    run()
# created on 2023-04-16
