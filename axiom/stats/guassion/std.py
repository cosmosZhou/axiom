from util import *


@apply
def apply():
    x = Symbol.x(real=True)
    return Equal(1 / sqrt(2 * pi) * Integral(exp(-x * x / 2), (x, -oo, oo)), 1, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra
    Eq << apply()

    Eq << Eq[0] * sqrt(2 * pi)

    x, *_ = Eq[-1].lhs.limits[0]
    y = Symbol.y(real=True)

    Eq << Eq[-1].lhs.this.limits_subs(x, y)

    Eq << Eq[-1] * Eq[-1].lhs

    Eq << Eq[-1].this.rhs.as_multiple_limits()

    Eq << Eq[-1].this.rhs.as_polar_coordinate()

    Eq << Eq[-1].this.rhs.doit()

    Eq << Eq[-1].apply(algebra.eq.imply.eq.sqrt)


# https://ccjou.wordpress.com/2012/11/26/jacobian-矩陣與行列式/
if __name__ == '__main__':
    run()
