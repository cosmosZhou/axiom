from util import *


@apply
def apply(given, index=-1):
    x, args = given.of(Expr <= Min)
    if index is None:
        eqs = [x <= arg for arg in args]
    else:
        first = args[:index]
        second = args[index:]
        eqs = x <= Min(*first), x <= Min(*second)

    return And(*eqs)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(x <= Min(y, z))

    Eq << Algebra.Iff.of.And.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Le_Min.to.And.Le)

    Eq << Eq[-1].this.rhs.apply(Algebra.Le.Le.to.Le.Min)


if __name__ == '__main__':
    run()
# created on 2022-01-01
