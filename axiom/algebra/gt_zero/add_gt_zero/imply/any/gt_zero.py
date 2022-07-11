from util import *


@apply
def apply(gt_zero, add_gt_zero, x=None):
    a = gt_zero.of(Expr > 0)
    b, (S[a], c) = add_gt_zero.of(Expr ** 2 - 4 * Expr * Expr > 0)
    assert x.is_real
    assert a.is_real and b.is_real and c.is_real
    return Any[x](a * x ** 2 + b * x + c > 0)


@prove
def prove(Eq):
    from axiom import algebra

    a, b, c = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(a > 0, b ** 2 - 4 * a * c > 0, x=x)

    Eq << algebra.gt.imply.ge.relax.apply(Eq[1])

    Eq << algebra.gt_zero.add_ge_zero.imply.any.gt_zero.apply(Eq[0], Eq[-1], x=x)


if __name__ == '__main__':
    run()
# created on 2022-04-03
