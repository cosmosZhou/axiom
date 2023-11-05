from util import *


@apply
def apply(self, var=None):
    expr = self.of(ReducedArgMin)
    return Equal(self, ReducedArgMax(-expr))


@prove(provable=False)
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    f = Function(real=True, shape=())
    i = Symbol(integer=True)
    Eq << apply(ReducedArgMin(Lamda[i:n](f(i))))

    Eq << Eq[0].this.lhs.apply(algebra.reducedArgMin.to.argmin)

    Eq << Eq[-1].this.rhs.apply(algebra.reducedArgMax.to.argmax)

    


if __name__ == '__main__':
    run()
# created on 2023-11-05
