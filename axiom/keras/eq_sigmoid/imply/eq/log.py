from util import *


@apply
def apply(given):
    x, y = given.of(Equal[sigmoid])

    return Equal(x, log(y / (1 - y)))


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True)
    Eq << apply(Equal(y, sigmoid(x)))

    Eq << Eq[0].this.rhs.defun()

    Eq << algebra.eq.imply.eq.inverse.apply(Eq[-1])

    Eq << Eq[-1] - 1

    Eq << Eq[-1].this.lhs.apply(algebra.add.to.mul.together)

    Eq << algebra.eq.imply.eq.log.apply(Eq[-1])

    Eq << -Eq[-1]

    Eq << Eq[-1].reversed

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.log)


if __name__ == '__main__':
    run()
# created on 2023-10-06
