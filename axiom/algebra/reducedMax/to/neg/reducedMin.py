from util import *


@apply
def apply(self, var=None):
    expr = self.of(ReducedMax)
    return Equal(self, -ReducedMin(-expr))




@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(oo,))
    Eq << apply(ReducedMax(x[:n]))

    Eq << Eq[0].this.find(ReducedMin).apply(algebra.reducedMin.to.neg.reducedMax)


if __name__ == '__main__':
    run()
# created on 2023-11-12
