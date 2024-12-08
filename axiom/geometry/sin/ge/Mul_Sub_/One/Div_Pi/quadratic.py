from util import *


@apply
def apply(x):
    return sin(x) >= x * (1 - x / S.Pi)

@prove
def prove(Eq):
    from Axiom import Algebra, Geometry

    x = Symbol(real=True)
    Eq << apply(x)

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[0], cond=x >= 0)

    Eq << Eq[-2].this.lhs.apply(Geometry.Ge_0.to.GeSin.quadratic)
    Eq << (x <= 0).this.apply(Geometry.Le_0.to.GeSin.quadratic)

    Eq << Eq[-1].this.lhs.apply(Algebra.Le.of.Lt)




if __name__ == '__main__':
    run()
# created on 2023-10-03
