from util import *


@apply
def apply(x):
    return Less(x, Floor(x) + 1)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(real=True)
    Eq << apply(x)

    Eq << algebra.imply.gt.floor.apply(x)

    Eq << Eq[-1] + 1

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2018-06-17
