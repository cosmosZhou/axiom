from util import *


@apply
def apply(is_positive_x, strict_greater_than):
    x = is_positive_x.of(Expr > 0)
    lhs, rhs = strict_greater_than.of(Greater)
    return Greater(lhs / x, rhs / x)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)

    Eq << apply(x > 0, a > b)


    Eq << algebra.is_positive.imply.is_positive.div.apply(Eq[0])

    Eq << algebra.is_positive.gt.imply.gt.mul.apply(Eq[-1], Eq[1])




if __name__ == '__main__':
    run()