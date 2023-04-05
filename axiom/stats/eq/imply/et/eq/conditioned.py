from util import *


@apply
def apply(given):
    (joint, *weights), _joint = given.of(Equal[Probability[Conditioned], Probability])
    if isinstance(_joint, tuple):
        joint, given = joint
        S[(joint, *weights)] = _joint
    else:
        assert _joint == joint
        [given] = weights
        weights = []

    return tuple(Equal(Probability(cond, *weights, given=given), Probability(cond, *weights)) for cond in joint.of(And))


@prove
def prove(Eq):
    from axiom import stats, calculus

    x, y, z = Symbol(real=True, random=True)
    Eq << apply(Equal(Probability(x & y | z), Probability(x, y)))

    Eq <<= Eq[-2].this.lhs.apply(stats.prob.to.mul.bayes), Eq[-1].this.lhs.apply(stats.prob.to.mul.bayes)

    Eq << Eq[0].this.lhs.apply(stats.prob.to.mul.bayes)

    Eq <<= calculus.eq.imply.eq.integral.apply(Eq[-1], (y.var,)), calculus.eq.imply.eq.integral.apply(Eq[-1], (x.var,))

    Eq <<= Eq[-2].this.rhs.apply(stats.integral.to.prob), Eq[-1].this.rhs.apply(stats.integral.to.prob)

    Eq <<= Eq[-2].this.find(Integral).apply(stats.integral.to.prob), Eq[-1].this.find(Integral).apply(stats.integral.to.prob)




if __name__ == '__main__':
    run()
# created on 2023-03-23
# updated on 2023-03-24
