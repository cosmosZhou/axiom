from util import *


@apply
def apply(self):
    arg, *args = self.of(Min)
    this = self.func(*args)
    rhs = Piecewise((arg, this >= arg), (this, True))

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y = Symbol(real=True)
    Eq << apply(Min(x, y))

    Eq << Eq[-1].this.find(GreaterEqual).reversed
    Eq << Eq[-1].this.lhs.apply(Algebra.Min.eq.Ite)


if __name__ == '__main__':
    run()
# created on 2020-01-26
