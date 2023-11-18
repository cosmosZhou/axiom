from util import *


@apply
def apply(x):
    return sin(x) >= x * (1 - x / S.Pi)

@prove
def prove(Eq):
    from axiom import algebra, geometry

    x = Symbol(real=True)
    Eq << apply(x)

    Eq << algebra.cond.given.et.infer.split.apply(Eq[0], cond=x >= 0)

    Eq << Eq[-2].this.lhs.apply(geometry.ge_zero.imply.sin_ge.quadratic)
    Eq << (x <= 0).this.apply(geometry.le_zero.imply.sin_ge.quadratic)

    Eq << Eq[-1].this.lhs.apply(algebra.le.given.lt)

    


if __name__ == '__main__':
    run()
# created on 2023-10-03
