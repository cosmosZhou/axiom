from util import *


@apply
def apply(lt, index=-1):
    args, x = lt.of(Max < Expr)
    first = args[:index]
    second = args[index:]

    return Less(Max(*first), x), Less(Max(*second), x)


@prove
def prove(Eq):
    from axiom import algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(Max(y, z) < x)

    Eq << algebra.lt_max.then.lt.apply(Eq[0], index=0)

    Eq << algebra.lt_max.then.lt.apply(Eq[0], index=1)


if __name__ == '__main__':
    run()
# created on 2020-01-11
