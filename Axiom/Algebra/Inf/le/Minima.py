from util import *


@apply
def apply(self):
    fx, *limits = self.of(Inf)
    return self <= Minima(fx, *limits)


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(real=True)
    S = Symbol(etype=dtype.real)
    f = Function(real=True)
    Eq << apply(Inf[x:S](f(x)))

    Eq << Eq[0].this.lhs.apply(Algebra.Inf.eq.ReducedMax)

    Eq << Eq[-1].this.lhs.apply(Algebra.ReducedMax.eq.Maxima)

    Eq << Algebra.LeMaxima.of.All.Le.apply(Eq[-1])

    Eq << Algebra.All.of.Imply.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Algebra.All_Ge.to.GeMinima)


if __name__ == '__main__':
    run()
# created on 2019-01-03
