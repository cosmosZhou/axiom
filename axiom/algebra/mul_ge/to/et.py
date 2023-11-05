from util import *


@apply
def apply(given):
    factor, cond = given.of(GreaterEqual[Mul[Bool], 1])
    return factor >= 1, cond


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(GreaterEqual(Bool(f(x) >= 0) * y, 1))

    Eq << algebra.iff.given.et.infer.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.mul_ge.imply.et)

    Eq << Eq[-1].this.rhs.apply(algebra.mul_ge.given.et)


if __name__ == '__main__':
    run()
# created on 2023-11-05
