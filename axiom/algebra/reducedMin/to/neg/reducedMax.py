from util import *


@apply
def apply(self, var=None):
    expr = self.of(ReducedMin)
    return Equal(self, -ReducedMax(-expr))




@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(oo,))
    Eq << apply(ReducedMin(x[:n]))

    Eq << Eq[-1].this.lhs.apply(algebra.reducedMin.to.minima)

    Eq << Eq[-1].this.find(ReducedMax).apply(algebra.reducedMax.to.maxima)

    Eq << Eq[-1].this.find(Maxima).apply(algebra.maxima.to.neg.minima)


if __name__ == '__main__':
    run()
# created on 2023-11-12
