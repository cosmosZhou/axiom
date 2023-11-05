from util import *


@apply
def apply(given):
    lhs, rhs = given.of(LessEqual)
    assert lhs.is_integer
    return Less(lhs, rhs + 1)


@prove
def prove(Eq):
    from axiom import algebra
    x, y = Symbol(integer=True, given=True)
    Eq << apply(x <= y)
    
    Eq << algebra.lt.imply.le.strengthen.apply(Eq[1])


if __name__ == '__main__':
    run()
# created on 2023-11-05
