from util import *


@apply
def apply(self, *new_weights):
    expr, *limits = self.of(Expectation)
    assert not expr.is_Conditioned
    new_weights = [*new_weights]
    limits_weighted = []
    new_limits_weighted = []

    random_symbols = expr.random_symbols
    conds = []
    for i, (x, *weights) in enumerate(limits):
        vars_included = {v for v in random_symbols if x.index_contains(v)}
        if len(vars_included) == 1:
            var, = vars_included
            if x != var:
                x = var

        if weights:
            new_weight = new_weights.pop(0)
            if isinstance(new_weight, (list, tuple)):
                limits[i] = (x, *new_weight)
            else:
                limits[i] = (x, new_weight)

            limits_weighted.append((x, *weights))
            new_limits_weighted.append(limits[i])
        conds.append(Equal(x, x.surrogate))

    conds = And(*conds)
    return Equal(self,
                 Expectation(expr * Probability(conds, *limits_weighted) / Probability(conds, *new_limits_weighted), *limits))

@prove
def prove(Eq):
    from axiom import stats

    D = Symbol(integer=True, positive=True)
    #D denotes the size of the trainable weights
    x = Symbol(integer=True, random=True)
    θ, θ_quote = Symbol(real=True, shape=(D,))
    f = Function(real=True, shape=())
    Eq << apply(Expectation[x:θ](f(x)), θ_quote)

    Eq << Eq[-1].this.lhs.apply(stats.expect.to.sum)

    Eq << Eq[-1].this.rhs.apply(stats.expect.to.sum)




if __name__ == '__main__':
    run()
# created on 2023-03-24
from . import pdf
