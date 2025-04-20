from util import *


@apply
def apply(self, *, simplify=True):
    ecs = self.of(Ceil[Piecewise])
    ecs = [(Ceil(e), c) for e, c in ecs]

    return Equal(self, Piecewise(*ecs), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Algebra, Logic

    x = Symbol(real=True)
    g, h = Function(real=True)
    Eq << apply(Ceil(Piecewise((g(x), x > 0), (h(x), True))))

    Eq << Logic.Cond_Ite__Ite.given.And.ou.OrAndS.apply(Eq[0])

    Eq << Eq[-1].this.args[0].apply(Algebra.Cond.Cond.given.And.subs)

    Eq << Eq[-1].this.find(And).apply(Algebra.Cond.Cond.given.And.subs, invert=True)





if __name__ == '__main__':
    run()
# created on 2018-11-02
# updated on 2023-05-20
