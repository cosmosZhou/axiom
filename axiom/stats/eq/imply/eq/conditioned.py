from util import *


@apply
def apply(given, index=0):
    (joint, given), S[joint] = given.of(Equal[Probability[Conditioned], Probability])
    
    vars = []
    for cond in joint.of(And):
        x, x_var = cond.of(Equal)
        vars.append(x)

    v = vars[index]
    return Equal(v | given, v)


@prove
def prove(Eq):
    from axiom import stats

    x, y, z = Symbol(real=True, random=True)
    Eq << apply(Equal(Probability(x & y | z), Probability(x, y)))

    Eq << stats.eq.imply.et.eq.conditioned.apply(Eq[0])

    


if __name__ == '__main__':
    run()
# created on 2023-03-23
# updated on 2023-03-24
