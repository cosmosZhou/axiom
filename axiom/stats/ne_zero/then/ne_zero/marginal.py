from util import *


@apply
def apply(given):
    x, given = given.of(Unequal[Probability[Conditioned], 0])
    return Unequal(Probability(x), 0)


@prove
def prove(Eq):
    from axiom import stats

    x, y = Symbol(real=True, random=True)
    Eq << apply(Unequal(Probability(x | y), 0))

    Eq << stats.ne_zero.then.ne_zero.joint.apply(Eq[0])

    Eq << stats.ne_zero.then.et.ne_zero.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-07-22
