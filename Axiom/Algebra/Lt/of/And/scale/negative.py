from util import *


@apply
def apply(given, scale):
    lhs, rhs = given.of(Less)
    return lhs * scale > rhs * scale, scale < 0


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(Less(x, y), z)

    Eq << Algebra.Lt_0.Gt.to.Lt.Div.apply(Eq[2], Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-12-16
