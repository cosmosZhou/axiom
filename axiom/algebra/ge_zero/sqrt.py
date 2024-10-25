from util import *


@apply
def apply(given):
    x = given.of(Expr >= 0)
    return sqrt(x) >= 0


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True)
    Eq << apply(x >= 0)

    Eq << algebra.iff.of.et.infer.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.ge_zero.then.ge_zero.sqrt)

    Eq << Eq[-1].this.rhs.apply(algebra.ge_zero.of.ge_zero.sqrt)


if __name__ == '__main__':
    run()
# created on 2023-06-20
