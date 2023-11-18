from util import *


@apply
def apply(self):
    x, y = self.of(Covariance)
    if x.is_Conditioned:
        x, given = x.args
        y, S[given] = y.of(Conditioned)
    else:
        given = None

    rhs = Expectation(x.outer_product(y), given=given) - Expectation(x, given=given).outer_product(Expectation(y, given=given))
                
    return Equal(self, rhs)

@prove
def prove(Eq):
    from axiom import stats, algebra

    n = Symbol(integer=True, positive=True)
    x, y = Symbol(real=True, random=True, shape=(n,))
    t = Symbol(integer=True, probable=True)
    Eq << apply(Covariance(x, y, given=t))

    Eq << Eq[0].this.lhs.apply(stats.cov.to.expect)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add, deep=True)

    Eq << Eq[-1].this.lhs.apply(stats.expect.to.add)

    Eq << Eq[-1].this.find(Expectation[Conditioned[Mul]]).apply(stats.expect.to.mul)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Expectation[Conditioned[Add]]).apply(stats.expect.to.add)

    Eq << Eq[-1].this.find(Expectation[Conditioned[Add]]).apply(stats.expect.to.add)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Expectation[Conditioned[Mul]]).apply(stats.expect.to.mul)

    i = Symbol(domain=Range(n))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], i)

    j = Symbol(domain=Range(n))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], j)
    


if __name__ == '__main__':
    run()
# created on 2023-04-09
# updated on 2023-04-14
