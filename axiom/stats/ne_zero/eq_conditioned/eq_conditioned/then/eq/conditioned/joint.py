from util import *


@apply
def apply(ne_zero, z_given_x, z_given_y):
    x, y = ne_zero.of(Unequal[Probability[And], 0])
    (z, S[x]), S[z] = z_given_x.of(Equal[Conditioned])
    (S[z], S[y]), S[z] = z_given_y.of(Equal[Conditioned])
    return Equal(z | x & y, z)


@prove
def prove(Eq):
    from axiom import stats, algebra

    x, y, z = Symbol(real=True, random=True)
    Eq << apply(Unequal(Probability(x, y), 0), Equal(z | x, z), Equal(z | y, z))



    Eq << stats.ne_zero.eq_conditioned.then.eq.conditioned.joint.apply(Eq[0], Eq[1])

    Eq << algebra.eq.eq.then.eq.trans.apply(Eq[-1], Eq[2])


if __name__ == '__main__':
    run()
# created on 2023-04-05
