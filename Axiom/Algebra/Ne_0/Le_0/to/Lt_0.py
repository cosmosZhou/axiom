from util import *


@apply
def apply(is_nonzero, is_nonpositive):
    x = is_nonzero.of(Unequal[0])
    is_nonpositive.of(x <= 0)
    return Less(x, 0)


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(real=True, given=True)
    Eq << apply(Unequal(x, 0), LessEqual(x, 0))

    Eq << ~Eq[-1]

    Eq << Algebra.Ge_0.Le_0.to.Eq_0.apply(Eq[-1], Eq[1])

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2020-02-15