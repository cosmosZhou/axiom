from util import *


@apply
def apply(self):
    assert self.is_KL
    return GreaterEqual(self, 0, evaluate=False)


@prove
def prove(Eq):
    from Axiom import Stats, Algebra

    D = Symbol(integer=True, positive=True)
    θ, θ_quote = Symbol(real=True, shape=(D,))
    x = Symbol(random=True, integer=True)
    Eq << apply(KL(Probability[θ](x), Probability[θ_quote](x)))

    Eq << Eq[-1].this.find(KL).apply(Stats.KL.eq.Sum)

    Eq << Algebra.Log.ge.Sub_.One.Inv.apply(Eq[1].find(Log).arg)

    Eq << Algebra.Ge.to.Ge.Mul.apply(Eq[-1], Eq[1].find(Probability))

    x = Eq[1].lhs.variable
    Eq << Algebra.Ge.to.Ge.Sum.apply(Eq[-1], (x,))

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.Add)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Stats.Sum.eq.One)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Stats.Sum.eq.One)





if __name__ == '__main__':
    run()

# created on 2021-07-20
# updated on 2023-04-22
