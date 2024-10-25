from util import *


@apply
def apply(given):
    cond, S[0] = given.of(Unequal[Bool])
    return cond


@prove
def prove(Eq):
    from axiom import algebra

    a, b = Symbol(real=True)
    Eq << apply(Unequal(Bool(a > b), 0))

    Eq << algebra.ne_zero.then.gt_zero.apply(Eq[0])

    Eq << algebra.gt_zero.then.cond.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-11-05
