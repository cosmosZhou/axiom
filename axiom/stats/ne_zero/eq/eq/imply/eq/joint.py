from util import *


# given: Probability(x | z) = Probability(x) and Probability(y | z) = Probability(y)
# imply: Probability(x & y) | Probability(z) = Probability(x & y)
@apply
def apply(given_x, given_y, ne_zero):
    (x, z), S[x] = given_x.of(Equal[Conditioned])
    (y, S[z]), S[y] = given_y.of(Equal[Conditioned])
    t, t_var = ne_zero.of(Unequal[Probability[Equal], 0])
    assert t in {x, y}

    assert x.is_random and y.is_random and z.is_random
    return Equal(Probability(x, y, given=z), Probability(x, y))


@prove
def prove(Eq):
    from axiom import stats, algebra

    x, y, z = Symbol(real=True, random=True)
    Eq << apply(Equal(x | z, x), Equal(y | z, y), Unequal(Probability(y), 0))

    Eq << stats.eq.imply.eq.mul.apply(Eq[0])

    Eq.bayes_yz = stats.eq.imply.eq.mul.apply(Eq[1])

    Eq.z_is_nonzero = algebra.cond.imply.cond.domain_defined.apply(Eq[0])

    Eq.bayes_xyz = stats.ne_zero.imply.eq.bayes.apply(Eq.z_is_nonzero, x, y)

    Eq << Eq[2].subs(Eq[1].reversed)

    Eq.given_addition = stats.ne_zero.eq.imply.eq.conditioned.joint.st.conditioned.apply(Eq[0], Eq[-1])

    Eq << stats.ne_zero.imply.ne_zero.joint.apply(Eq[-1])

    Eq << stats.ne_zero.imply.eq.bayes.apply(Eq[-1], x)

    Eq << Eq.bayes_xyz.subs(Eq[-1])

    Eq << Eq[-1].subs(Eq.bayes_yz)

    Eq << algebra.ne_zero.eq.imply.eq.scalar.apply(Eq[-1], Eq.z_is_nonzero)

    Eq << Eq[-1].subs(Eq.given_addition)

    Eq << stats.ne_zero.imply.eq.bayes.apply(Eq[2], x)

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq[-1].reversed

    


if __name__ == '__main__':
    run()
# created on 2020-12-15
# updated on 2023-04-05
