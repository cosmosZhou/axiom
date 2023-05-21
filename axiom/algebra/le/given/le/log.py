from util import *


@apply
def apply(lt):
    lhs, rhs = lt.of(LessEqual)
    return log(lhs) <= log(rhs)


@prove
def prove(Eq):
    from axiom import algebra
    
    x, y, z = Symbol(real=True, given=True)
    Eq << apply(LessEqual(x, y))
    
    Eq << algebra.le.imply.le.exp.apply(Eq[1])


if __name__ == '__main__':
    run()
# created on 2023-04-16
