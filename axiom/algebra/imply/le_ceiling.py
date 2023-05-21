from util import *


@apply
def apply(x, evaluate=False):
    return LessEqual(x, Ceiling(x), evaluate=evaluate)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True)
    Eq << apply(x)

    Eq << algebra.imply.ceiling_ge.apply(x)
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2018-10-28
