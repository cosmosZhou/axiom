from util import *


# given: Probability(x | y) != 0
# imply: Probability(x, y) != 0
@apply
def apply(given):
    lhs, rhs = given.of(Unequal[Probability[Conditioned], 0])
    return Unequal(Probability(lhs, rhs), 0)


@prove
def prove(Eq):
    from Axiom import Algebra, Stats

    x, y = Symbol(real=True, random=True)
    Eq << apply(Unequal(Probability(x | y), 0))

    Eq << Algebra.Cond.to.Cond.domain_defined.apply(Eq[0])

    Eq << Stats.Ne_0.to.Prob.eq.Mul.Prob.bayes.apply(Eq[-1], x)

    Eq << Algebra.Ne_0.Ne_0.to.Ne_0.Mul.apply(Eq[0], Eq[2])

    Eq << Eq[-1].subs(Eq[-2].reversed)




if __name__ == '__main__':
    run()
# created on 2020-12-11
# updated on 2023-04-05
