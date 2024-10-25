from util import *


@apply
def apply(ne, *vars):
    given = []
    rest = []
    vars = [*vars]

    args = ne.of(Unequal[Probability[And], 0])
    if args[-1].is_Tuple:
        args, *weights = args
    else:
        weights = []

    for cond in args:
        x, x_var = cond.of(Equal)
        if x in vars:
            rest.append(cond)
            vars.remove(x)
        else:
            given.append(cond)

    rest = And(*rest)
    given = And(*given)
    joint = And(*(Equal(x, x.var) for x in vars))
    return Equal(Probability(joint & rest, *weights, given=given), Probability(rest, *weights, given=given) * Probability(joint, *weights, given=rest & given))


@prove
def prove(Eq):
    from axiom import stats

    x, y, z = Symbol(real=True, random=True)
    Eq << apply(Unequal(Probability(y, z), 0), x, y)

    Eq << stats.ne_zero.then.ne_zero.conditioned.apply(Eq[0], z)

    Eq << stats.ne_zero.then.eq.bayes.conditioned.apply(Eq[-1], x)



if __name__ == '__main__':
    run()
# created on 2023-03-27
