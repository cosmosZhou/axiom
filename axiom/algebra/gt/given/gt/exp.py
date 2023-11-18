from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Greater)

    return Greater(exp(lhs), exp(rhs))


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True)
    Eq << apply(Greater(x, y))

    Eq << algebra.gt.imply.gt.log.apply(Eq[1])

    


if __name__ == '__main__':
    run()
# created on 2022-03-31
