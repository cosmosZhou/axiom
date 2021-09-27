from util import *


@apply
def apply(lt, gt):
    x, a = lt.of(Less)
    y, b = gt.of(Greater)

    return Less((x - a) * (y - b), 0)


@prove
def prove(Eq):
    from axiom import algebra

    x, y, a, b = Symbol(real=True)
    Eq << apply(x < a, y > b)

    Eq << Eq[1].reversed

    Eq << algebra.lt.lt.imply.is_positive.apply(Eq[0], Eq[-1])

    Eq << -Eq[-1]

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[2].this.lhs.expand()


if __name__ == '__main__':
    run()