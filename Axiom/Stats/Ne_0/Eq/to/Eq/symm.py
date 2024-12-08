from util import *


@apply
def apply(given_equality, ne_zero):
    x, x_var = ne_zero.of(Unequal[Probability[Equal], 0])

    (S[x], y), S[x] = given_equality.of(Equal[Conditioned])
    y, y_var = y.of(Equal)

    return Equal(y | x, y)


@prove
def prove(Eq):
    from Axiom import Stats
    x, y = Symbol(real=True, random=True)

    Eq << apply(Equal(x | y, x), Unequal(Probability(x), 0))

    Eq << Stats.Eq_Conditioned.to.Eq.Mul.Prob.apply(Eq[0])

    Eq << Stats.Ne_0.Eq.to.Eq.independence.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()
# created on 2021-07-16
