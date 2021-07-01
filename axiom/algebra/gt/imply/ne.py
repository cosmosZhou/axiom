from util import *


@apply
def apply(given):
    assert given.is_Greater
    
    return Unequal(*given.args)


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    Eq << apply(x > y)
    
    Eq << ~Eq[-1]
    Eq << Eq[0].subs(Eq[-1])
    

if __name__ == '__main__':
    run()