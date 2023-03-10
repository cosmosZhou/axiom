from util import *


@apply
def apply(x):
    return log(x) >= 1 - 1 / x


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True)
    Eq << apply(x)

    Eq << algebra.imply.le.log.apply(x)

    Eq << -Eq[-1]

    Eq << Eq[-1].subs(x, 1 / x)
    Eq << Eq[-1].this.find(Log).simplify()


if __name__ == '__main__':
    run()
# created on 2019-09-21
