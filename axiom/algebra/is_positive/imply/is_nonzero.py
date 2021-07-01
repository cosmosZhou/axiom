from util import *


@apply
def apply(given):
    x = given.of(Expr > 0)
    return Unequal(x, 0)


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    
    Eq << apply(x > 0)
    
    Eq << ~Eq[1]
    
    Eq <<= Eq[-1] & Eq[0]

    
if __name__ == '__main__':
    run()
