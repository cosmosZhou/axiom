from util import *


@apply
def apply(eq, *expr, spread_weight=False):
    assert expr
    condition = And(*(Equal(y, y.var) for y in expr))
    
    given_probability = eq.of(Unequal[0])
    cond = given_probability.of(Probability)

    if isinstance(cond, tuple):
        cond, weight = cond
        random_symbols = [v for v in cond.random_symbols if not v.is_Surrogate]
        if spread_weight:
            limits = [weight]
        else:
            limits = [(v, *weight) for v in random_symbols]
    else:
        limits = []

    return Equal(Probability(cond & condition, *limits), given_probability * Probability(condition, given=cond, *limits))


@prove
def prove(Eq):
    from axiom import stats

    x, y = Symbol(real=True, random=True)
    Eq << apply(Unequal(Probability(y), 0), x)

    Eq << Eq[-1].this.find(Probability[Conditioned]).apply(stats.prob.to.mul.bayes)


if __name__ == '__main__':
    run()

from . import conditioned
# created on 2020-12-09
