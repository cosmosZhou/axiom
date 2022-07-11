from util import *


@apply
def apply(any_lt_zero, x=None):
    f, (x,) = any_lt_zero.of(Any[Expr < 0])
    from axiom.algebra.le.ge.imply.le.quadratic import quadratic_coefficient
    x, a, b, c = quadratic_coefficient(f, x)
    assert x.is_real
    assert a.is_real and b.is_real and c.is_real
    return b ** 2 - 4 * a * c > 0


@prove
def prove(Eq):
    from axiom import algebra

    a, b, c = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(Any[x](a * x ** 2 + b * x + c < 0))

    Eq << algebra.add_gt_zero.imply.any.lt_zero.apply(Eq[1], x=x)

    


if __name__ == '__main__':
    run()
# created on 2022-04-03
