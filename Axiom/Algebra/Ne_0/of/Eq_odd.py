from util import *


@apply
def apply(given):
    expr = given.of(Unequal[0])
    n, S[2] = expr.of(Mod)
    return Equal(expr, 1)


@prove
def prove(Eq):
    from Axiom import Algebra

    n = Symbol(integer=True)
    Eq << apply(Unequal(n % 2, 0))

    Eq << Algebra.Eq.to.Ne_0.apply(Eq[1])




if __name__ == '__main__':
    run()
# created on 2020-01-27
# updated on 2023-05-22
