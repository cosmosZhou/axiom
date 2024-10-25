from util import *


@apply
def apply(given, x):
    cond = given.of(Equal[Probability, 0])
    cond &= Equal(x, x.var)
    return Equal(Probability(cond), 0)


@prove
def prove(Eq):
    from axiom import stats, algebra

    x, y = Symbol(real=True, random=True)
    Eq << apply(Equal(Probability(x), 0), y)

    Eq << Eq[1].invert().this.apply(stats.ne_zero.then.ne_zero.delete)

    Eq << Eq[-1].this.apply(algebra.infer.contraposition)

    Eq << algebra.cond.infer.then.cond.trans.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-03-21
