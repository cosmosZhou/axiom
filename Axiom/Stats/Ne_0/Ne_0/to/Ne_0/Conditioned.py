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
    from Axiom import Stats, Algebra

    x, y = Symbol(random=True, integer=True)
    Eq << apply(Unequal(Probability(y), 0),
                Unequal(Probability(x, y), 0))

    Eq << Stats.Ne_0.to.Prob.eq.Mul.Prob.bayes.apply(Eq[0], x)

    Eq << Algebra.Ne_0.Eq.to.Eq.Div.apply(Eq[0], Eq[-1])

    Eq << Algebra.Ne_0.Ne_0.to.Ne_0.Div.apply(Eq[1], Eq[0])

    Eq << Algebra.Ne.Eq.to.Ne.trans.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2023-03-22
