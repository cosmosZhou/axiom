from util import *



@apply
def apply(given):
    x, y = given.of(LessEqual)
    assert y < 0
    return Less(x, 0)


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True, negative=True)
    Eq << apply(x <= y)
    
    Eq << ~Eq[1]
    
    Eq <<= Eq[-1] & Eq[0]
    

if __name__ == '__main__':
    run()
