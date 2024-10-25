from util import *


@apply
def apply(given, index=-1):
    [*eqs] = given.of(Unequal[Probability[And], 0])

    del eqs[index]

    eq = And(*eqs)

    return Unequal(Probability(eq), 0)


@prove
def prove(Eq):
    from axiom import stats, algebra, calculus

    x, y = Symbol(real=True, random=True)
    Eq << apply(Unequal(Probability(x, y), 0))

    Eq.y_marginal_probability = stats.integral.to.prob.marginal.apply(Integral[y.var](Probability(x, y)))

    Eq << algebra.ne_zero.then.gt_zero.apply(Eq[0])

    Eq << calculus.gt.then.gt.integral.apply(Eq[-1], (y.var,))

    Eq << Eq[-1].subs(Eq.y_marginal_probability)

    Eq <<= algebra.gt.then.ne.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2020-12-12
# updated on 2023-04-28
