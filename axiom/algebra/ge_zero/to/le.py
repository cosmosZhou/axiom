from util import *


@apply
def apply(given):
    x, y = given.of(Expr - Expr >= 0)
    return LessEqual(y, x)


@prove
def prove(Eq):
    from axiom import algebra

    a, b = Symbol(real=True, given=True)
    Eq << apply(LessEqual(0, a - b))

    Eq << algebra.iff.of.et.infer.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.ge_zero.then.le)

    Eq << Eq[-1].this.rhs.apply(algebra.ge_zero.of.le)


if __name__ == '__main__':
    run()
# created on 2023-06-20
