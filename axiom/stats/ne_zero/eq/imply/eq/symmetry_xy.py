from util import *


@apply
def apply(given_equality, ne_zero):
    et = ne_zero.of(Unequal[Probability, 0])
    
    (x, y), S[x] = given_equality.of(Equal[Conditioned])
    y, y_var = y.of(Equal)
    
    vars = {eq.of(Equal)[0] for eq in et.of(And)}
    
    assert x in vars and y in vars
    return Equal(y | x, y)


@prove
def prove(Eq):
    from axiom import stats

    x, y = Symbol(real=True, random=True)
    Eq << apply(Equal(x | y, x), Unequal(Probability(x, y), 0))

    Eq << stats.ne_zero.imply.et.ne_zero.apply(Eq[1])



    Eq << stats.ne_zero.eq.imply.eq.symmetry.apply(Eq[0], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2021-07-16
