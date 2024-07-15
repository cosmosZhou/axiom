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
    Eq << stats.ne_zero.imply.ne_zero.joint_slice.apply(Eq[1], [i, None])

    Eq << stats.ne_zero.eq.imply.eq.mul.prod.prob.conditioned.apply(Eq[0], Eq[-1])

    Eq << algebra.eq.imply.eq.argmin.apply(Eq[-1], (i,))

    


if __name__ == '__main__':
    run()
# created on 2021-07-21
# updated on 2024-06-18
