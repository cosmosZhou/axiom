from util import *


@apply
def apply(sup):
    fx, *limits = sup.of(Sup)
    return sup >= Maxima(fx, *limits)


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(real=True)
    S = Symbol(etype=dtype.real)
    f = Function(real=True)
    Eq << apply(Sup[x:S](f(x)))

    Eq << Eq[0].this.lhs.apply(Algebra.Sup.eq.ReducedMin)

    Eq << Eq[-1].this.lhs.apply(Algebra.ReducedMin.eq.Minima)

    Eq << Algebra.GeMinima.of.All.Ge.apply(Eq[-1])

    Eq << Algebra.All.of.Imply.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Algebra.All_Le.to.LeMaxima)


if __name__ == '__main__':
    run()
# created on 2019-09-21
