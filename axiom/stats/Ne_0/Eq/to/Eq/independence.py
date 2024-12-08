from util import *


@apply
def apply(equality, inequality):
    lhs, rhs = equality.of(Equal)
    x = inequality.of(Unequal[Probability, 0])

    _x, y = lhs.of(Probability).args

    if x != _x:
        S[x], y = y, _x

    assert rhs == Probability(x) * Probability(y)
    return Equal(Probability(y, given=x), Probability(y))


@prove
def prove(Eq):
    from Axiom import Stats, Algebra

    x, y = Symbol(real=True, random=True)
    given = Equal(Probability(x, y), Probability(x) * Probability(y))
    Eq << apply(given, Unequal(Probability(x), 0))

    Eq << Eq[-1].simplify()

    Eq << Stats.Ne_0.to.Prob.eq.Mul.Prob.bayes.apply(Eq[1], y)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1] - Eq[-1].rhs

    Eq << Eq[-1].this.lhs.collect(Probability(x))

    Eq << Algebra.Mul.eq.Zero.to.OrEqS_0.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[1]

    Eq << Algebra.And.to.And.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-07-15
