from util import *


@apply
def apply(self):
    args = self.of(asin[Piecewise])
    ecs = [(asin(e), c) for e, c in args]
    return Equal(self, Piecewise(*ecs))


@prove
def prove(Eq):
    from Axiom import Algebra, Logic

    x = Symbol(real=True)
    A = Symbol(etype=dtype.real)
    f, g = Function(real=True)
    Eq << apply(asin(Piecewise((f(x), Element(x, A)), (g(x), True))))

    Eq << Logic.Cond_Ite__Ite.given.And.ou.OrAndS.apply(Eq[0])

    Eq << Eq[-1].this.find(And).apply(Algebra.Cond.Cond.given.And.subs)

    Eq << Eq[-1].this.find(And).apply(Algebra.Cond.Cond.given.And.subs, invert=True)




if __name__ == '__main__':
    run()
# created on 2022-01-20
# updated on 2023-04-30
