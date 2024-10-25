from util import *


@apply
def apply(self):
    fx, *limits = self.of(Inf)
    return self <= Minima(fx, *limits)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True)
    S = Symbol(etype=dtype.real)
    f = Function(real=True)
    Eq << apply(Inf[x:S](f(x)))

    Eq << Eq[0].this.lhs.apply(algebra.inf.to.reducedMax)

    Eq << Eq[-1].this.lhs.apply(algebra.reducedMax.to.maxima)

    Eq << algebra.maxima_le.of.all.le.apply(Eq[-1])

    Eq << algebra.all.of.infer.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(algebra.all_ge.then.minima_ge)


if __name__ == '__main__':
    run()
# created on 2019-01-03
