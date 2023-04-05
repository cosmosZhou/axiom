from util import *


@apply
def apply(self):
    fx, *limits = self.of(Variance)
    return Equal(self,
                 Expectation(fx ** 2, *limits) - Expectation(fx, *limits) ** 2)

@prove
def prove(Eq):
    from axiom import stats

    x = Symbol(integer=True, random=True)
    Eq << apply(Variance[x](x))

    Eq << Eq[-1].this.lhs.apply(stats.var.to.expect)

    Eq << Eq[-1].this.find(Add ** 2).expand()

    Eq << Eq[-1].this.lhs.apply(stats.expect.to.add)

    Eq << Eq[-1].this.find(Expectation[Mul]).apply(stats.expect.to.mul)




if __name__ == '__main__':
    run()
# created on 2023-03-24
