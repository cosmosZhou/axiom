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
    from Axiom import Stats, Algebra

    m, n, t = Symbol(integer=True, positive=True)
    # suppose you have a set of documents y which is labeled with some semantic tags called keywords x;
    # now that there is a large data set consisting of pairs of y and its respective set of keywords x;
    # you are then given a new document y', how to figure out the way of choosing the keywords x with optimal probability?
    x = Symbol(integer=True, shape=(n,), random=True)
    y = Symbol(integer=True, shape=(m,), random=True)
    Eq << apply(Equal(y[t] | y[:t], y[t]), Unequal(Probability(y, x), 0))

    j = Eq[-1].find(Product).variable
    Eq << Stats.Ne_0.to.Eq.Prob.Conditioned.eq.Div.Prob.Conditioned.bayes.apply(Eq[1])

    Eq << Stats.Ne_0.to.Ne_0.joint_slice.apply(Eq[1], [None, slice(0, t)])

    Eq.yt_given_y_historic = Stats.Ne_0.Eq_Conditioned.to.Eq.Conditioned.joint.apply(Eq[0], Eq[-1])

    Eq.yt_given_x_nonzero = Stats.Ne_0.to.Ne_0.Conditioned.apply(Eq[-1], x)

    Eq << Stats.Ne_0.to.Eq.bayes.Conditioned.apply(Eq.yt_given_x_nonzero, y[t])

    Eq << Eq[-1].this.lhs.find(And).apply(Algebra.Eq.Eq.to.Eq.concat)

    Eq << Eq[-1].subs(Eq.yt_given_y_historic)

    Eq << Algebra.Ne_0.Eq.to.Eq.scalar.apply(Eq[-1], Eq.yt_given_x_nonzero)

    Eq << Algebra.Eq.to.Eq.Prod.apply(Eq[-1], (t, 1, m))

    t = Eq[-1].rhs.variable
    Eq << Eq[-1] * Eq[-1].find(Pow).base

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul.eq.Prod.limits.unshift)

    Eq << Eq[-1].this.rhs.limits_subs(t, j)

    Eq << Eq[2].subs(Eq[-1].reversed)

    Eq << Algebra.And.of.And.apply(Eq[-1])

    Eq << Stats.Ne_0.to.Ne_0.delete.apply(Eq[1], 0)




if __name__ == '__main__':
    run()
# created on 2024-06-18
