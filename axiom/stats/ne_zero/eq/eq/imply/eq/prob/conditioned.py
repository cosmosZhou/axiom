from util import *


@apply
def apply(given_x, given_y, ne):
    (x, z), S[x] = given_x.of(Equal[Conditioned])

    (y, S[z]), S[y] = given_y.of(Equal[Conditioned])

    S[x & y] = ne.of(Unequal[Probability, 0])

    assert x.is_random and y.is_random and z.is_random
    return Equal(Probability(x & y, given=z), Probability(x, y))


@prove
def prove(Eq):
    from axiom import stats

    x, y, z = Symbol(real=True, random=True)
    Eq << apply(x.is_independent_of(z), y.is_independent_of(z), Unequal(Probability(x, y), 0))

    Eq << stats.ne_zero.imply.et.ne_zero.apply(Eq[2])


    Eq << stats.ne_zero.eq.eq.imply.eq.joint.apply(Eq[0], Eq[1], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-12-16
