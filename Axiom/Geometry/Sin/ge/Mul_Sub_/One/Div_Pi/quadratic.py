from util import *


@apply
def apply(x):
    return sin(x) >= x * (1 - x / S.Pi)

@prove
def prove(Eq):
    from Axiom import Algebra, Geometry, Logic

    x = Symbol(real=True)
    Eq << apply(x)

    Eq << Logic.Cond.given.And.Imp.split.apply(Eq[0], cond=x >= 0)

    Eq << Eq[-2].this.lhs.apply(Geometry.GeSin.of.Ge_0.quadratic)
    Eq << (x <= 0).this.apply(Geometry.GeSin.of.Le_0.quadratic)

    Eq << Eq[-1].this.lhs.apply(Algebra.Le.given.Lt)




if __name__ == '__main__':
    run()
# created on 2023-10-03
