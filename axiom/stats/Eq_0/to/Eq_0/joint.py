from util import *


@apply
def apply(given, x):
    cond = given.of(Equal[Probability, 0])
    cond &= Equal(x, x.var)
    return Equal(Probability(cond), 0)


@prove
def prove(Eq):
    from Axiom import Stats, Algebra

    x, y = Symbol(real=True, random=True)
    Eq << apply(Equal(Probability(x), 0), y)

    Eq << Eq[1].invert().this.apply(Stats.Ne_0.to.Ne_0.delete)

    Eq << Eq[-1].this.apply(Algebra.Imply.contraposition)

    Eq << Algebra.Cond.Imply.to.Cond.trans.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-03-21
