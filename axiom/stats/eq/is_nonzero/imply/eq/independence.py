from util import *


@apply
def apply(*given):
    equality, inequality = given
    lhs, rhs = equality.of(Equal)
    x = inequality.of(Unequal[Probability, 0])

    _x, y = lhs.of(Probability).args

    if x != _x:
        _x, y = y, _x
    assert x == _x
    assert rhs == Probability(x) * Probability(y)

    return Equal(Probability(y, given=x), Probability(y))


@prove
def prove(Eq):
    from axiom import stats, algebra
    x = Symbol.x(real=True, random=True)
    y = Symbol.y(real=True, random=True)

    given = Equal(Probability(x, y), Probability(x) * Probability(y))

    Eq << apply(given, Unequal(Probability(x), 0))

    Eq << Eq[-1].simplify()

    Eq << stats.bayes.corollary.apply(Eq[1], var=y)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1] - Eq[-1].rhs

    Eq << Eq[-1].this.lhs.collect(Probability(x))

    Eq << algebra.is_zero.imply.ou.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[1]

    Eq << algebra.et.imply.conds.apply(Eq[-1])


if __name__ == '__main__':
    run()
