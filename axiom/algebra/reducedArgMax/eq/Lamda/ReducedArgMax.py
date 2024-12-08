from util import *


@apply
def apply(self):
    fx, *limits = self.of(ReducedArgMax[Lamda])
    if fx.shape:
        return Equal(self, Lamda(ReducedArgMax(fx), *limits))

    limit, *limits = limits
    return Equal(self, Lamda(ReducedArgMax(Lamda(fx, limit)), *limits))


@prove
def prove(Eq):
    from Axiom import Algebra

    m, n = Symbol(integer=True, positive=True)
    f = Function(real=True, shape=(m,))
    i = Symbol(integer=True)
    x = Symbol(real=True)
    Eq << apply(ReducedArgMax(Lamda[i:n](f(x))))

    i = Symbol(domain=Range(n))
    Eq << Algebra.Eq.of.Eq.getitem.apply(Eq[0], i)



if __name__ == '__main__':
    run()
# created on 2021-12-17
