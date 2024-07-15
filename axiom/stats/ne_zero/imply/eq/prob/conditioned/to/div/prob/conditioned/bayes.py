from util import *


@apply
def apply(given, index=-1):
    eqs = given.of(Unequal[Probability[And], 0])

    if eqs[-1].is_Tuple:
        eqs, *weights = eqs
    else:
        weights = []

    lhs, rhs = std.array_split(eqs, index)
    lhs = And(*lhs)
    rhs = And(*rhs)
    return Equal(Probability(lhs, *weights, given=rhs), Probability(rhs, *weights, given=lhs) * Probability(lhs, *weights) / Probability(rhs, *weights))


@prove
def prove(Eq):
    from axiom import stats, algebra

    x, y = Symbol(real=True, random=True)
    Eq << apply(Unequal(Probability(x, y), 0))

    Eq << stats.ne_zero.imply.et.ne_zero.apply(Eq[0])

    Eq <<= stats.ne_zero.imply.eq.prob.to.mul.prob.bayes.apply(Eq[-2], y), stats.ne_zero.imply.eq.prob.to.mul.prob.bayes.apply(Eq[-1], x)

    Eq << algebra.ne_zero.eq.imply.eq.scalar.apply(Eq[-1], Eq[-3]).reversed

    Eq << Eq[-1].subs(Eq[-3])




if __name__ == '__main__':
    run()
# created on 2024-06-18
# updated on 2024-06-20
