from util import *


@apply
def apply(given):
    (fx, *limits), M = given.of(Less[Maxima])
    return All(fx < M, *limits)


@prove
def prove(Eq):
    from Axiom import Algebra

    M, x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Maxima[x:a:b](f(x)) < M)

    Eq << Algebra.All_Lt.to.LtMaxima.apply(Eq[1])




if __name__ == '__main__':
    run()
# created on 2023-11-12
