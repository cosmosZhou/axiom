from util import *


@apply
def apply(self, *vars):
    given = S.true
    for v in vars:
        given &= Equal(v, v.surrogate)
        assert v.is_probable

    expr, *limits_v = self.of(Variance)
    return Equal(self,
                 Variance(Expectation(expr | given, *limits_v)) + Expectation(Variance(expr | given, *limits_v)))

@prove
def prove(Eq):
    from axiom import stats

    n = Symbol(integer=True, positive=True)
    y = Symbol(real=True, random=True, shape=(n,))
    x = Symbol(real=True, probable=True)
    Eq << apply(Variance(y), x)

    Eq << Eq[0].this.rhs.find(Variance).apply(stats.var.expect.to.sub.expect)

    Eq << Eq[-1].this.find(Expectation[Variance]).apply(stats.expect.var.to.sub.expect)

    Eq << Eq[-1].this.find(Variance).apply(stats.var.to.sub.expect)





if __name__ == '__main__':
    run()
# created on 2023-04-09
# updated on 2023-04-14
