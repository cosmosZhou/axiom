from util import *


@apply
def apply(lt_zero, lt):
    a, b = lt.of(Less)
    x = lt_zero.of(Expr < 0)
    return lt_zero, Greater((a / x).expand(), (b / x).expand()).simplify()


@prove
def prove(Eq):
    from axiom import algebra
    
    x, y, z = Symbol(integer=True)
    Eq << apply(x < 0, Less(x + y, z))
    
    Eq << algebra.lt_zero.gt.imply.lt.mul.apply(Eq[0], Eq[2])
    
    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.add)


if __name__ == '__main__':
    run()
# created on 2023-10-03
