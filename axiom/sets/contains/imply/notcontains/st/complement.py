from util import *


@apply
def apply(given):
    e, domain = given.of(Contains)
    S, s = domain.of(Complement)
    
    return NotContains(e, s)


@prove
def prove(Eq):
    e = Symbol.e(integer=True, given=True)
    s = Symbol.s(etype=dtype.integer, given=True)
    
    S = Symbol.S(etype=dtype.integer, given=True)
    
    Eq << apply(Contains(e, S // s, evaluate=False))
    
    Eq << ~Eq[-1]
    
    Eq <<= Eq[0] & Eq[-1]


if __name__ == '__main__':
    run()
