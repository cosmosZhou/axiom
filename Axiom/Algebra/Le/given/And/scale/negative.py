from util import *


@apply
def apply(given, scale):
    lhs, rhs = given.of(LessEqual)
    return lhs * scale >= rhs * scale, scale < 0


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(LessEqual(x, y), z)

    Eq << Algebra.LeDiv.of.Lt_0.Ge.apply(Eq[2], Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-10-28
