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
    from Axiom import Stats, Algebra

    x, y = Symbol(real=True, random=True)
    Eq << apply(Unequal(Probability(x, y), 0))

    Eq << Stats.Ne_0.to.And.Ne_0.apply(Eq[0])

    Eq <<= Stats.Ne_0.to.Prob.eq.Mul.Prob.bayes.apply(Eq[-2], y), Stats.Ne_0.to.Prob.eq.Mul.Prob.bayes.apply(Eq[-1], x)

    Eq << Algebra.Ne_0.Eq.to.Eq.scalar.apply(Eq[-1], Eq[-3]).reversed

    Eq << Eq[-1].subs(Eq[-3])




if __name__ == '__main__':
    run()
# created on 2024-06-18
# updated on 2024-06-20
