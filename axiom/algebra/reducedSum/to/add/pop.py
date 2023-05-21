from util import *


@apply
def apply(self):
    expr = self.of(ReducedSum)
    n = expr.shape[0]
    return Equal(self, ReducedSum(expr[:n - 1]) + expr[n - 1], evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    x, y = Symbol(shape=(oo,), real=True)
    Eq << apply(ReducedSum(x[:n + 1]))

    Eq << Eq[0].this.lhs.apply(algebra.reducedSum.to.sum)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add.pop)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.reducedSum)
    


if __name__ == '__main__':
    run()
# created on 2023-04-19
