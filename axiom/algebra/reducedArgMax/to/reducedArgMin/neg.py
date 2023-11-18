from util import *


@apply
def apply(self, var=None):
    expr = self.of(ReducedArgMax)
    return Equal(self, ReducedArgMin(-expr))


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    f = Function(real=True, shape=())
    i = Symbol(integer=True)
    Eq << apply(ReducedArgMax(Lamda[i:n](f(i))))

    Eq << Eq[0].this.rhs.apply(algebra.reducedArgMin.to.reducedArgMax.neg)

    


if __name__ == '__main__':
    run()
# created on 2023-11-05
