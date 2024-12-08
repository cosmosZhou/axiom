from util import *


@apply
def apply(self, var=None):
    expr, dist = self.of(Distributed)
    if var is None:
        if expr.is_symbol:
            var = expr.var
        else:
            var = dist.generate_var(shape=expr.shape, **expr.dtype.dict)

    return Equal(Probability(Equal(expr, var)), dist(var), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Stats

    x = Symbol(real=True, random=True)
    μ = Symbol(real=True)
    σ = Symbol(positive=True)
    Eq << apply(Distributed(x, NormalDistribution(μ, σ)))

    Eq << Eq[0].this.apply(Stats.Distributed.equ.Eq.Prob)


if __name__ == '__main__':
    run()
# created on 2023-04-30
