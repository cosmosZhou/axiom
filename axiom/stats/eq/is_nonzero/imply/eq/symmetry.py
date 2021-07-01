from util import *


# given: x | y = x
# imply: y | x = y
@apply
def apply(*given):
    given_equality, unequal = given
    assert unequal.is_Unequal
    assert unequal.lhs.is_Probability
    assert unequal.rhs.is_zero

    assert given_equality.is_Equal
    lhs, rhs = given_equality.args
    assert lhs.is_Conditioned
    x, y = lhs.args
    assert x == rhs

    if y.is_Equal:
        y = y.lhs
    assert y.is_random and y.is_symbol
    return Equal(y | x, y)


@prove
def prove(Eq):
    from axiom import stats
    x = Symbol.x(real=True, random=True)
    y = Symbol.y(real=True, random=True)

    given = Equal(x | y, x)

    Eq << apply(given, Unequal(Probability(x), 0))

    Eq << stats.eq.imply.eq.mul.apply(given)

    Eq << stats.eq.is_nonzero.imply.eq.independence.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()