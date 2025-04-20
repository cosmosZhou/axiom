from util import *



@apply
def apply(unequality, equality):
    divisor = unequality.of(Unequal[0])
    lhs, rhs = equality.of(Equal)
    return Equal(lhs / divisor, rhs / divisor)


@prove
def prove(Eq):
    from Axiom import Algebra
    x, a, b = Symbol(real=True)
    Eq << apply(Unequal(x, 0), Equal(x * a, b))

    Eq << Eq[1] / x
    Eq <<= Eq[-1] & Eq[0]

    Eq << Algebra.And.of.And.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-08-13
