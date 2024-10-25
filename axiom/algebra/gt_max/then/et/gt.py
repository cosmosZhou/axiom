from util import *


@apply
def apply(gt, index=-1):
    x, args = gt.of(Expr > Max)
    first = args[:index]
    second = args[index:]

    return Greater(x, Max(*first)), Greater(x, Max(*second))


@prove
def prove(Eq):
    from axiom import algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(x > Max(y, z))

    Eq << algebra.gt_max.then.gt.apply(Eq[0], index=0)

    Eq << algebra.gt_max.then.gt.apply(Eq[0], index=1)





if __name__ == '__main__':
    run()
# created on 2019-08-04
# updated on 2022-01-01