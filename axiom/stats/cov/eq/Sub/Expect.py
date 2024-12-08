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
    from Axiom import Stats, Algebra

    n = Symbol(integer=True, positive=True)
    x, y = Symbol(real=True, random=True, shape=(n,))
    t = Symbol(integer=True, probable=True)
    Eq << apply(Covariance(x, y, given=t))

    Eq << Eq[0].this.lhs.apply(Stats.Cov.eq.Expect)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul.eq.Add, deep=True)

    Eq << Eq[-1].this.lhs.apply(Stats.Expect.eq.Add)

    Eq << Eq[-1].this.find(Expectation[Conditioned[Mul]]).apply(Stats.Expect.eq.Mul)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.find(Expectation[Conditioned[Add]]).apply(Stats.Expect.eq.Add)

    Eq << Eq[-1].this.find(Expectation[Conditioned[Add]]).apply(Stats.Expect.eq.Add)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.find(Expectation[Conditioned[Mul]]).apply(Stats.Expect.eq.Mul)

    i = Symbol(domain=Range(n))
    Eq << Algebra.Eq.of.Eq.getitem.apply(Eq[-1], i)

    j = Symbol(domain=Range(n))
    Eq << Algebra.Eq.of.Eq.getitem.apply(Eq[-1], j)



if __name__ == '__main__':
    run()
# created on 2023-04-09
# updated on 2023-04-14
