from util import *


@apply
def apply(eq, ne):
    x_boolean, y_boolean = ne.of(Unequal[Probability[And], 0])

    ((x, t), S[x[:t].as_boolean()]), S[x[t]] = eq.of(Equal[Conditioned[Indexed]])

    if x_boolean != x.as_boolean():
        x_boolean, y_boolean = y_boolean, x_boolean

    y = y_boolean.lhs

    assert t > 0
    j = Symbol(integer=True)
    return Equal(Probability(y | x), Probability(y) * Product[j](Probability(x[j] | y)) / Probability(x))


@prove
def prove(Eq):
    from axiom import stats, algebra

    m, n, t = Symbol(integer=True, positive=True)
    # suppose you have a set of documents y which is labeled with some semantic tags called keywords x;
    # now that there is a large data set consisting of pairs of y and its respective set of keywords x;
    # you are then given a new document y', how to figure out the way of choosing the keywords x with optimal probability?
    x = Symbol(integer=True, shape=(n,), random=True)
    y = Symbol(integer=True, shape=(m,), random=True)
    Eq << apply(Equal(y[t] | y[:t], y[t]), Unequal(Probability(y, x), 0))

    j = Eq[-1].find(Product).variable
    Eq << stats.ne_zero.imply.eq.prob.conditioned.to.div.prob.conditioned.bayes.apply(Eq[1])

    Eq << stats.ne_zero.imply.ne_zero.joint_slice.apply(Eq[1], [None, slice(0, t)])

    Eq.yt_given_y_historic = stats.ne_zero.eq_conditioned.imply.eq.conditioned.joint.apply(Eq[0], Eq[-1])

    Eq.yt_given_x_nonzero = stats.ne_zero.imply.ne_zero.conditioned.apply(Eq[-1], x)

    Eq << stats.ne_zero.imply.eq.bayes.conditioned.apply(Eq.yt_given_x_nonzero, y[t])

    Eq << Eq[-1].this.lhs.find(And).apply(algebra.eq.eq.imply.eq.concat)

    Eq << Eq[-1].subs(Eq.yt_given_y_historic)

    Eq << algebra.ne_zero.eq.imply.eq.scalar.apply(Eq[-1], Eq.yt_given_x_nonzero)

    Eq << algebra.eq.imply.eq.prod.apply(Eq[-1], (t, 1, m))

    t = Eq[-1].rhs.variable
    Eq << Eq[-1] * Eq[-1].find(Pow).base

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.prod.limits.unshift)

    Eq << Eq[-1].this.rhs.limits_subs(t, j)

    Eq << Eq[2].subs(Eq[-1].reversed)

    Eq << algebra.et.given.et.apply(Eq[-1])

    Eq << stats.ne_zero.imply.ne_zero.delete.apply(Eq[1], 0)




if __name__ == '__main__':
    run()
# created on 2024-06-18
