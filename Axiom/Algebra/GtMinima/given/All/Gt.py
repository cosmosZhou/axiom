from util import *


@apply
def apply(given):
    (fx, *limits), M = given.of(Greater[Minima])
    return All(fx > M, *limits)


@prove
def prove(Eq):
    from Axiom import Algebra

    M, x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Minima[x:a:b](f(x)) > M)

    Eq << Algebra.GtMinima.of.All_Gt.apply(Eq[1])




if __name__ == '__main__':
    run()
# created on 2023-11-12
