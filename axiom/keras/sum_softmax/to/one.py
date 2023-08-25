from util import *


@apply
def apply(self):
    x = self.of(ReducedSum[Softmax])

    return Equal(self, OneMatrix(*x.shape[:-1]))


@prove
def prove(Eq):
    from axiom import algebra

    m, n = Symbol(integer=True, positive=True)
    x = Symbol(shape=(m, n), real=True)
    Eq << apply(ReducedSum(Softmax(x)))

    Eq << Eq[-1].this.lhs.apply(algebra.reducedSum.to.sum)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.lamda)

    Eq << Eq[-1].this.find(ReducedSum).apply(algebra.reducedSum.to.sum)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.limits.domain_defined)






if __name__ == '__main__':
    run()
# created on 2023-03-18
# updated on 2023-05-06
