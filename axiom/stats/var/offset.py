from util import *


@apply
def apply(self):
    (x, (S[x], (S[x],))), (S[x],) = self.of(Variance[Expr - Expectation])
    return Equal(self, Variance[x](x))

@prove
def prove(Eq):
    from axiom import stats, algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, random=True, shape=(n,))
    Eq << apply(Variance[x](x - Expectation(x)))

    Eq << Eq[0].lhs.this.apply(stats.var.to.expect)

    Eq << Eq[-1].this.rhs.find(Expectation[Add]).apply(stats.expect.to.add)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.rhs.find(Expectation[Add]).apply(stats.expect.to.add)

    Eq << Eq[-1].this.rhs.find(Expectation[Add]).apply(stats.expect.to.add)

    Eq << Eq[0].this.rhs.apply(stats.var.to.expect)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(algebra.mul.to.add)
    


if __name__ == '__main__':
    run()
# created on 2023-04-09
# updated on 2023-04-14
