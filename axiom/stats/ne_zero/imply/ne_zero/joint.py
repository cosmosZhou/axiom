from util import *


# given: Probability(x | y) != 0
# imply: Probability(x, y) != 0
@apply
def apply(given):
    lhs, rhs = given.of(Unequal[Probability[Conditioned], 0])
    return Unequal(Probability(lhs, rhs), 0)


@prove
def prove(Eq):
    from axiom import algebra, stats

    x, y = Symbol(real=True, random=True)
    Eq << apply(Unequal(Probability(x | y), 0))

    Eq << algebra.cond.imply.cond.domain_defined.apply(Eq[0])

    Eq << stats.ne_zero.imply.eq.bayes.apply(Eq[-1], x)

    Eq << algebra.ne_zero.ne_zero.imply.ne_zero.mul.apply(Eq[0], Eq[2])

    Eq << Eq[-1].subs(Eq[-2].reversed)

    


if __name__ == '__main__':
    run()
# created on 2020-12-11
# updated on 2023-04-05
