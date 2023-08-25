from util import *


@apply
def apply(ne, eq):
    a, b = eq.of(Equal)
    x = ne.of(Unequal[0])
    return Unequal(x, 0), Equal((a / x).expand(), (b / x).expand()).simplify()


@prove
def prove(Eq):
    from axiom import algebra

    x, y, z = Symbol(integer=True)
    Eq << apply(Unequal(x, 0), Equal(x + y, z))

    Eq << algebra.ne_zero.eq.imply.eq.mul.apply(Eq[0], Eq[2])

    
    


if __name__ == '__main__':
    run()
# created on 2023-03-26
# updated on 2023-06-22
