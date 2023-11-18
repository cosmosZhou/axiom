from util import *


@apply
def apply(self):
    from axiom.algebra.reducedSum.to.sum import rewrite
    from axiom.algebra.sum.to.add.doit import doit
    return Equal(self, doit(Sum, rewrite(self)))


@prove
def prove(Eq):
    from axiom import algebra

    k = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(oo,))
    n = 5
    Eq << apply(ReducedSum(x[:n]))

    Eq << Eq[-1].this.lhs.apply(algebra.reducedSum.to.sum)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add.doit)

    


if __name__ == '__main__':
    run()
# created on 2023-08-20
