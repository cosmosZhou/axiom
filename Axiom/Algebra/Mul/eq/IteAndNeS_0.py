from util import *


@apply
def apply(self):
    args = self.of(Mul)
    return Equal(self, Piecewise((self, And(*(Unequal(arg, 0) for arg in args))), (0, True)))


@prove
def prove(Eq):
    from Axiom import Algebra, Logic

    x, y = Symbol(real=True)
    Eq << apply(x * y)

    Eq << Logic.Cond_Ite__Ite.given.And.ou.OrAndS.apply(Eq[0])

    Eq << Eq[-1].this.args[1].apply(Algebra.AndNeS_0.given.Mul.ne.Zero)

    Eq << Eq[-1].this.find(Or).apply(Algebra.OrEqS_0.given.Mul.eq.Zero)





if __name__ == '__main__':
    run()
# created on 2018-01-30
# updated on 2025-04-12
