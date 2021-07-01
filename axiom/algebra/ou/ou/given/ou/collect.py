from util import *


@apply
def apply(*eqs, cond=None):
    matched = []
    unmatch = []
    
    for eq in eqs:
        if eq.is_Or:
            if cond in eq.args:
                matched.append(Or(*eq._argset - {cond}))
                continue
        elif eq == cond:
            matched.append(S.false)
            continue
        unmatch.append(eq)
    assert not unmatch
    return Or(cond, And(*matched))


@prove
def prove(Eq):
    a = Symbol.a(integer=True, given=True)
    b = Symbol.b(integer=True, given=True)
    c = Symbol.c(integer=True, given=True)
    d = Symbol.d(integer=True, given=True)
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    f = Function.f(real=True)
    g = Function.g(real=True)
    Eq << apply((a < b) | (c < d), (f(x) < g(y)) | (c < d), (x < y) | (c < d), cond=c < d)

    Eq <<= Eq[0] & Eq[1] & Eq[2]

    

    


if __name__ == '__main__':
    run()