from util import *


@apply
def apply(self):
    from axiom.stats.sum.to.expect import rewrite
    return Equal(self, rewrite(Integral, self))


@prove
def prove(Eq):
    from axiom import stats

    n = Symbol(integer=True, positive=True)
    θ = Symbol(real=True, shape=(n, n))
    f = Function(real=True)
    x, s = Symbol(real=True, random=True)
    Eq << apply(Integral[x.var](Probability[x:θ](x | s) * f(x.var)))

    Eq << Eq[-1].this.rhs.apply(stats.expect.to.integral)

    


if __name__ == '__main__':
    run()
# created on 2023-04-02
