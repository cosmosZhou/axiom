from util import *


@apply
def apply(self):
    x = self.of(Abs)
    return Equal(self, Piecewise((x, x > 0), (-x, True)))


@prove
def prove(Eq):
    from Axiom import Algebra, Logic
    x = Symbol(real=True)
    Eq << apply(abs(x))

    Eq << Algebra.Abs.eq.IteGe_0.apply(abs(x))

    Eq << Eq[-1].subs(x, -x)

    Eq << -Eq[-1].this.rhs.args[0].cond

    Eq << Eq[-1].this.rhs.apply(Logic.Ite__Ite.eq.IteAnd_Not__Ite, -2)


if __name__ == '__main__':
    run()
# created on 2018-01-18
