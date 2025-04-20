from util import *


@apply
def apply(self):
    fx, (x, a, b) = self.of(Integral)

    return Equal(self, Piecewise((-Integral[x:Interval(b, a)](fx), a > b), (Integral[x:Interval(a, b)](fx), True)))


@prove
def prove(Eq):
    from Axiom import Calculus, Algebra, Logic

    x, a, b = Symbol(real=True)
    f = Function(real=True, integrable=True)
    Eq << apply(Integral[x:a:b](f(x)))

    Eq << Eq[0].this.rhs.find(Integral).apply(Calculus.IntegralIcc.eq.Ite)

    Eq << Eq[-1].this.rhs.args[1].expr.apply(Calculus.IntegralIcc.eq.Ite)

    Eq << Eq[-1].this.find(-Piecewise).apply(Algebra.Mul.eq.Ite)

    Eq << Eq[-1].this.rhs.apply(Logic.Ite_Ite.eq.Ite__Ite)

    Eq << Eq[-1].this.rhs.args[1].cond.reversed

    Eq << Eq[-1].this.rhs.args[0].expr.apply(Calculus.Neg.eq.Integral)

    Eq << Eq[-1].this.rhs.apply(Logic.Ite__Ite.eq.IteAnd_Not__Ite, -2)

    Eq << Logic.Cond_Ite__Ite.given.And.ou.OrAndS.apply(Eq[-1])

    Eq << Eq[-1].this.find(And).apply(Algebra.Eq.Cond.given.And.subs)





if __name__ == '__main__':
    run()


# created on 2020-05-24
# updated on 2023-08-26
del Limit
from . import Limit
