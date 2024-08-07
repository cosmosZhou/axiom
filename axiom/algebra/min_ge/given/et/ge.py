from util import *


@apply
def apply(ge, index=-1):
    args, x = ge.of(Min >= Expr)
    first = args[:index]
    second = args[index:]

    return Min(*first) >= x, Min(*second) >= x


@prove
def prove(Eq):
    from axiom import algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(Min(y, z) >= x)

    Eq << algebra.ge.ge.imply.ge.min.apply(Eq[1], Eq[2])

    


if __name__ == '__main__':
    run()
# created on 2023-03-26
