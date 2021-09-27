from util import *


@apply
def apply(given, upper=None, lower=None):
    lhs, rhs = given.of(LessEqual)
    
    if upper is not None:
        assert upper >= rhs
        rhs = upper
    elif lower is not None:
        assert lower <= lhs
        lhs = lower
    
    return LessEqual(lhs, rhs)


@prove
def prove(Eq):
    x, y = Symbol(real=True, given=True)
    Eq << apply(LessEqual(x, y), y + 1)

    Eq << ~Eq[1]

    Eq <<= Eq[0] & Eq[-1]

    #Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

