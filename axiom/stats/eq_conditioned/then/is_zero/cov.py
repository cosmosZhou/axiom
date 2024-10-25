from util import *


@apply
def apply(eq_conditioned, swap=False):
    (y, x), S[y] = eq_conditioned.of(Equal[Conditioned])
    x, x_var = x.of(Equal)
    if swap:
        x, y = y, x
    return Equal(Covariance(x, y), ZeroMatrix(*x.shape).outer_product(ZeroMatrix(*y.shape)))


@prove
def prove(Eq):
    from axiom import stats

    x, y = Symbol(real=True, random=True)
    Eq << apply(Equal(y | x, y))

    Eq << Eq[1].this.lhs.apply(stats.cov.to.sub.expect)

    Eq << stats.eq_conditioned.then.eq.mul.expect.apply(Eq[0])

    Eq << Eq[-1].reversed




if __name__ == '__main__':
    run()
# created on 2023-04-19
