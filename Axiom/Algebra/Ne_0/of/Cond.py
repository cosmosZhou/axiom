from util import *


@apply
def apply(given):
    cond, S[0] = given.of(Unequal[Bool])
    return cond


@prove
def prove(Eq):
    from Axiom import Algebra

    a, b = Symbol(real=True)
    Eq << apply(Unequal(Bool(a > b), 0))

    Eq << Algebra.Ne_0.of.Gt_0.apply(Eq[0])

    Eq << Algebra.Gt_0.of.Cond.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-11-05
