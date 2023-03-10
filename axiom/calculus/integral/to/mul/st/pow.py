from util import *


@apply
def apply(n, a=0, b=None, x=None):
    assert n.is_integer

    if x is None:
        x = Symbol(real=True)

    return Equal(Integral(x ** n, (x, a, b)), (b ** (n + 1) - a * (n + 1)) / (n + 1))


@prove
def prove(Eq):
    from axiom import calculus, algebra

    x = Symbol(real=True)
    n = Symbol(integer=True, nonnegative=True)
    Eq << apply(n, b=x)

    f = Symbol(Eq[0].lhs)
    g = Symbol(Eq[0].rhs)
    Eq << diff(f, x).this.expr.definition

    Eq << Eq[-1].this.rhs.doit()

    Eq.df = Eq[-1].this.rhs.powsimp()

    Eq << diff(g, x).this.expr.definition

    Eq << Eq[-1].this.rhs.doit()

    Eq << Eq[-1].this.rhs.powsimp()

    Eq << Eq.df - Eq[-1]

    Eq << Eq[-1].this.lhs.apply(calculus.add.to.derivative)

    Eq << calculus.is_zero.imply.any_eq.constant.apply(Eq[-1])

    Eq << Eq[-1].this.expr.expr.lhs.args[0].definition

    Eq << Eq[-1].this.find(-~Symbol).definition

    Eq << algebra.any_all.imply.any_et.subs.apply(Eq[-1], x, 0)

    Eq << Eq[-1].this.expr.expr.args[1].lhs.doit()

    Eq << Eq[-1].this.expr.expr.apply(algebra.eq.eq.imply.eq.transit)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2020-06-12
