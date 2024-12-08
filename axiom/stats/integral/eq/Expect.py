from util import *


@apply
def apply(self):
    from Axiom.Stats.Sum.eq.Expect import rewrite
    return Equal(self, rewrite(Integral, self))


@prove
def prove(Eq):
    from Axiom import Stats

    n = Symbol(integer=True, positive=True)
    θ = Symbol(real=True, shape=(n, n))
    f = Function(real=True)
    x, s = Symbol(real=True, random=True)
    Eq << apply(Integral[x.var](Probability[x:θ](x | s) * f(x.var)))

    Eq << Eq[-1].this.rhs.apply(Stats.Expect.eq.Integral)




if __name__ == '__main__':
    run()
# created on 2023-04-02
