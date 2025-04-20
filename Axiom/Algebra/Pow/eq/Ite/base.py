from util import *


@apply
def apply(self):
    ecs, t = self.of(Piecewise ** Expr)
    return Equal(self, Piecewise(*((e ** t, c) for e, c in ecs)))


@prove
def prove(Eq):
    from Axiom import Algebra, Logic

    n = Symbol(integer=True)
    A = Symbol(etype=dtype.real)
    x, t = Symbol(real=True)
    g, h = Function(real=True)
    Eq << apply(Pow(Piecewise((g(x), Element(x, A)),(h(x), True)), t, evaluate=False))

    Eq << Logic.Cond_Ite__Ite.given.And.ou.OrAndS.apply(Eq[0])

    Eq << Eq[-1].this.args[0].apply(Algebra.Cond.Cond.given.And.subs)

    Eq << Eq[-1].this.find(And).apply(Algebra.Cond.Cond.given.And.subs, invert=True)





if __name__ == '__main__':
    run()
# created on 2020-02-29
# updated on 2023-05-14
