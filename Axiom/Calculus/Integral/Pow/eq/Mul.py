from util import *


@apply
def apply(self):
    (x, n), (S[x], a, b) = self.of(Integral[Pow])
    return Equal(self, (b ** (n + 1) - a * (n + 1)) / (n + 1))


@prove
def prove(Eq):
    from Axiom import Calculus, Algebra

    x = Symbol(real=True)
    n = Symbol(integer=True, nonnegative=True)
    Eq << apply(Integral[x:0:x](x ** n))

    f = Symbol(Eq[0].lhs)
    g = Symbol(Eq[0].rhs)
    Eq << diff(f, x).this.expr.definition

    Eq << Eq[-1].this.rhs.doit()

    Eq.df = Eq[-1].this.rhs.powsimp()

    Eq << diff(g, x).this.expr.definition

    Eq << Eq[-1].this.rhs.doit()

    Eq << Eq[-1].this.rhs.powsimp()

    Eq << Eq.df - Eq[-1]

    Eq << Eq[-1].this.lhs.apply(Calculus.Add.eq.Grad)

    Eq << Calculus.Eq_0.to.Any.Eq.constant.apply(Eq[-1])

    Eq << Eq[-1].this.expr.expr.lhs.args[0].definition

    Eq << Eq[-1].this.find(-~Symbol).definition

    Eq << Algebra.Any_All.to.Any.And.subs.apply(Eq[-1], x, 0)

    Eq << Eq[-1].this.expr.expr.args[1].lhs.doit()

    Eq << Eq[-1].this.expr.expr.apply(Algebra.Eq.Eq.to.Eq.trans)

    Eq << Eq[-1].reversed





if __name__ == '__main__':
    run()

# created on 2020-06-12
# updated on 2023-04-30
