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
    from Axiom import Stats

    x, y = Symbol(real=True, random=True)
    Eq << apply(Equal(y | x, y))

    Eq << Eq[1].this.lhs.apply(Stats.Cov.eq.Sub.Expect)

    Eq << Stats.Eq_Conditioned.to.Eq.Mul.Expect.apply(Eq[0])

    Eq << Eq[-1].reversed




if __name__ == '__main__':
    run()
# created on 2023-04-19
