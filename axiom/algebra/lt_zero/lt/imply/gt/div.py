from util import *


@apply
def apply(lt_zero, lt):
    x = lt_zero.of(Expr < 0)
    assert x.is_finite
    lhs, rhs = lt.of(Less)
    lhs /= x
    rhs /= x
    lhs = lhs.ratsimp()
    rhs = rhs.ratsimp()
    return Greater(lhs, rhs)


@prove
def prove(Eq):
    from axiom import algebra

    x, a, b = Symbol(real=True)
    Eq << apply(x < 0, a < b)

    Eq << algebra.lt_zero.imply.lt_zero.div.apply(Eq[0])

    Eq << algebra.lt_zero.lt.imply.gt.mul.apply(Eq[-1], Eq[1])

    
    


if __name__ == '__main__':
    run()
# created on 2019-07-15
# updated on 2023-04-11
