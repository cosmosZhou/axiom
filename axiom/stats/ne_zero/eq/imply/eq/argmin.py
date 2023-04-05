from util import *


@apply
def apply(eq, ne):
    x_boolean, y_boolean = ne.of(Unequal[Probability[And], 0])

    ((x, t), S[x[:t].as_boolean()]), S[x[t]] = eq.of(Equal[Conditioned[Indexed]])

    if x_boolean != x.as_boolean():
        x_boolean, y_boolean = y_boolean, x_boolean

    y = y_boolean.lhs

    assert t > 0
    i, j = Symbol(integer=True)
    return Equal(ArgMin[i](Probability(y[i] | x)), ArgMin[i](Probability(y[i]) * Product[j](Probability(x[j] | y[i]))))


@prove
def prove(Eq):
    from axiom import stats, algebra

    t, n, m = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,), random=True)
    y = Symbol(real=True, shape=(m,), random=True)
    Eq << apply(Equal(y[t] | y[:t], y[t]), Unequal(Probability(y, x), 0))

    i = Eq[-1].lhs.variable
    j = Eq[-1].rhs.expr.args[-1].variable
    Eq << stats.ne_zero.imply.et.ne_zero.apply(Eq[1])

    Eq << stats.ne_zero.imply.eq.bayes.apply(Eq[-1], x[i])

    Eq.x_given_p = algebra.ne_zero.eq.imply.eq.scalar.apply(Eq[-1], Eq[-2]).reversed

    Eq << stats.ne_zero.imply.ne_zero.joint_slice.apply(Eq[1], [i, j])

    Eq << stats.ne_zero.imply.et.ne_zero.apply(Eq[-1])

    Eq << stats.ne_zero.imply.eq.bayes.apply(Eq[-2], y)

    Eq.x_given_p = Eq.x_given_p.subs(Eq[-1])

    Eq << algebra.eq.imply.eq.argmin.apply(Eq.x_given_p, (i,))

    Eq << stats.ne_zero.imply.ne_zero.joint_slice.apply(Eq[1], [i, slice(0, t)])

    Eq.yt_given_y_historic = stats.ne_zero.eq.imply.eq.conditioned.joint.apply(Eq[0], Eq[-1])

    Eq.yt_given_xi_nonzero = stats.ne_zero.imply.ne_zero.conditioned.apply(Eq[-1], x[i])

    Eq << stats.ne_zero.imply.eq.bayes.conditioned.apply(Eq.yt_given_xi_nonzero, y[t])

    Eq << Eq[-1].this.lhs.find(And).apply(algebra.eq.eq.imply.eq.concat)

    Eq << Eq[-1].subs(Eq.yt_given_y_historic)

    Eq << algebra.ne_zero.eq.imply.eq.scalar.apply(Eq[-1], Eq.yt_given_xi_nonzero)

    Eq << algebra.eq.imply.eq.prod.apply(Eq[-1], (t, 1, m))

    t = Eq[-1].rhs.variable
    Eq << Eq[-1] * Eq[-1].find(Pow).base

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.prod.limits.unshift)

    Eq << Eq[-1].this.rhs.limits_subs(t, j)

    Eq << Eq[2].subs(Eq[-1].reversed)




if __name__ == '__main__':
    run()
# created on 2021-07-21
# updated on 2023-03-22
