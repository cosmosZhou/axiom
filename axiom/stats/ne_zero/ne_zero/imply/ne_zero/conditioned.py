from util import *


@apply
def apply(ne_zero_given, ne_zero_joint):

    vars_given = set()
    given = ne_zero_given.of(Unequal[Probability, 0])
    if conds := given.of(And):
        ...
    else:
        conds = [given]

    for cond in conds:
        x, x_var = cond.of(Equal)
        vars_given.add(x)

    vars_joint = set()
    for cond in ne_zero_joint.of(Unequal[Probability[And], 0]):
        x, x_var = cond.of(Equal)
        vars_joint.add(x)

    vars = vars_joint - vars_given
    return Unequal(Probability(*vars, given=And(*(var.as_boolean() for var in vars_given))), 0)


@prove
def prove(Eq):
    from axiom import stats, algebra

    x, y = Symbol(random=True, integer=True)
    Eq << apply(Unequal(Probability(y), 0),
                Unequal(Probability(x, y), 0))

    Eq << stats.ne_zero.imply.eq.prob.to.mul.prob.bayes.apply(Eq[0], x)

    Eq << algebra.ne_zero.eq.imply.eq.div.apply(Eq[0], Eq[-1])

    Eq << algebra.ne_zero.ne_zero.imply.ne_zero.div.apply(Eq[1], Eq[0])

    Eq << algebra.ne.eq.imply.ne.transit.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2023-03-22
