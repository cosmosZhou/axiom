from util import *


@apply
def apply(self):
    fx, *limits = self.of(Expectation[Expr ** 2])

    return Equal(self,
                 Expectation(fx, *limits) ** 2 + Variance(fx, *limits))

@prove
def prove(Eq):
    from axiom import stats

    x = Symbol(integer=True, random=True)
    Eq << apply(Expectation[x](x ** 2))

    Eq << Eq[-1].this.find(Variance).apply(stats.var.to.sub.expect)




if __name__ == '__main__':
    run()
# created on 2023-03-24
