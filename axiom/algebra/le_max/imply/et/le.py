from util import *


@apply
def apply(le, index=-1):
    args, x = le.of(Max <= Expr)
    first = args[:index]
    second = args[index:]
    
    return LessEqual(Max(*first), x), LessEqual(Max(*second), x)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    z = Symbol.z(real=True, given=True)
    Eq << apply(Max(y, z) <= x)

    Eq << algebra.le_max.imply.le.apply(Eq[0], index=0)

    Eq << algebra.le_max.imply.le.apply(Eq[0], index=1)


if __name__ == '__main__':
    run()