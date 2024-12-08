from util import *


@apply
def apply(given, *wrt):
    assert wrt
    probability = given.of(Unequal[Expr, 0])
    p = probability.marginalize(*wrt)

    return Unequal(Probability(p.arg, given=And(*(w.as_boolean() for w in wrt))), 0)


@prove
def prove(Eq):
    from Axiom import Stats, Algebra

    x, y, z = Symbol(real=True, random=True)
    Eq << apply(Unequal(Probability(x, y, z), 0), y, z)

    Eq << Stats.Ne_0.to.And.Ne_0.apply(Eq[0], 1)

    Eq << Stats.Ne_0.to.Prob.eq.Mul.Prob.bayes.apply(Eq[-1], x)

    Eq << Eq[0].subs(Eq[-1])

    Eq << Algebra.Ne_0.Ne.to.Ne.scalar.apply(Eq[-3], Eq[-1])





if __name__ == '__main__':
    run()
# created on 2020-12-10
# updated on 2023-03-22
