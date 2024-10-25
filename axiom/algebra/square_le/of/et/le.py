from util import *


@apply
def apply(given):
    abs_x, a = given.of(LessEqual)
    x = abs_x.of(Expr ** 2)
    assert x.is_real
    return LessEqual(x, sqrt(a)), LessEqual(-sqrt(a), x)


@prove
def prove(Eq):
    from axiom import algebra

    x, a = Symbol(real=True)
    Eq << apply(x ** 2 <= a ** 2)

    Eq << algebra.le.ge.then.le.abs.apply(Eq[-2], Eq[-1].reversed)

    Eq << algebra.le.then.le.square.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-06-18
