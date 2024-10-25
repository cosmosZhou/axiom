from util import *


@apply
def apply(gt, lt):
    x, y = lt.of(Less)
    S[x], S[-y] = gt.of(Greater)
    return Less(abs(x), y)


@prove
def prove(Eq):
    from axiom import algebra

    y, x = Symbol(real=True)
    Eq << apply(x > -y, x < y)

    Eq << algebra.lt.gt.then.lt.abs.apply(Eq[1], Eq[0])




if __name__ == '__main__':
    run()
# created on 2023-04-15
