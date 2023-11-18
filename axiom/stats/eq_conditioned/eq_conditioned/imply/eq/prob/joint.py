from util import *


@apply
def apply(x_given_z, y_given_z):
    (x, z), S[x] = x_given_z.of(Equal[Conditioned])
    (y, S[z]), S[y] = y_given_z.of(Equal[Conditioned])

    return Equal(Probability(x & y, given=z), Probability(x & y))


@prove(provable=False)
def prove(Eq):
    from axiom import algebra

    x, y, z = Symbol(real=True, random=True)
    Eq << apply(Equal(x | z, x), Equal(y | z, y))

    Eq << algebra.cond.given.et.infer.split.apply(Eq[-1], cond=Equal(Probability(x), 0))

    Eq << algebra.cond.infer.imply.infer.et.lhs.apply(Eq[0] & Eq[1], Eq[-1])

    

    


if __name__ == '__main__':
    run()
# created on 2023-04-01
# updated on 2023-04-05
