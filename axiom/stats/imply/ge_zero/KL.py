from util import *


@apply
def apply(self):
    assert self.is_KL
    return GreaterEqual(self, 0, evaluate=False)


@prove
def prove(Eq):
    from axiom import stats, algebra

    D = Symbol(integer=True, positive=True)
    θ, θ_quote = Symbol(real=True, shape=(D,))
    x = Symbol(random=True, integer=True)
    Eq << apply(KL(Probability[θ](x), Probability[θ_quote](x)))

    Eq << Eq[-1].this.find(KL).apply(stats.KL.to.sum)

    Eq << algebra.imply.ge.log.apply(Eq[1].find(Log).arg)

    Eq << algebra.ge.imply.ge.mul.apply(Eq[-1], Eq[1].find(Probability))

    x = Eq[1].lhs.variable
    Eq << algebra.ge.imply.ge.sum.apply(Eq[-1], (x,))

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add)

    Eq << Eq[-1].this.rhs.find(Sum).apply(stats.sum.to.one)

    Eq << Eq[-1].this.rhs.find(Sum).apply(stats.sum.to.one)

    
    


if __name__ == '__main__':
    run()

# created on 2021-07-20
# updated on 2023-04-22
