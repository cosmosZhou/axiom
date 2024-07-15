from util import *


@apply
def apply(given, *wrt):
    assert wrt
    probability = given.of(Unequal[Expr, 0])
    p = probability.marginalize(*wrt)

    return Unequal(Probability(p.arg, given=And(*(w.as_boolean() for w in wrt))), 0)


@prove
def prove(Eq):
    from axiom import stats, algebra

    x, y, z = Symbol(real=True, random=True)
    Eq << apply(Unequal(Probability(x, y, z), 0), y, z)

    Eq << stats.ne_zero.imply.et.ne_zero.apply(Eq[0], 1)

    Eq << stats.ne_zero.imply.eq.prob.to.mul.prob.bayes.apply(Eq[-1], x)

    Eq << Eq[0].subs(Eq[-1])

    Eq << algebra.ne_zero.ne.imply.ne.scalar.apply(Eq[-3], Eq[-1])





if __name__ == '__main__':
    run()
# created on 2020-12-10
# updated on 2023-03-22
