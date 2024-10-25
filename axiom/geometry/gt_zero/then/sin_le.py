from util import *


@apply
def apply(ge_zero):
    x = ge_zero.of(Expr > 0)
    return sin(x) <= x

@prove
def prove(Eq):
    from axiom import algebra, geometry

    x = Symbol(real=True)
    Eq << apply(x > 0)

    Eq << algebra.gt.then.ge.relax.apply(Eq[0])

    Eq << geometry.ge_zero.then.sin_le.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-10-03
