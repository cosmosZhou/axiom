from util import *


@apply
def apply(le, sgm):
    _b, _a = le.of(Less)
    expr, (k, a, b) = sgm.of(Sum)
    assert _a == a and _b == b
    return Equal(sgm, 0)


@prove
def prove(Eq):
    from axiom import algebra

    a, b = Symbol(integer=True, given=True)
    n = Symbol(integer=True)
    f = Function(integer=True)
    Eq << apply(b < a, Sum[n:a:b](f(n)))

    Eq << algebra.lt.imply.le.relax.apply(Eq[0])
    Eq << algebra.le.imply.sum_is_zero.apply(Eq[-1], Eq[1].lhs)


if __name__ == '__main__':
    run()
# created on 2020-01-04
