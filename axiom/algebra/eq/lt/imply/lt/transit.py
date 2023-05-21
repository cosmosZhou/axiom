from util import *


@apply
def apply(eq, lt):
    a, x = eq.of(Equal)
    _x, y = lt.of(Less)
    if x != _x:
        S[a] = _x

    return a < y


@prove
def prove(Eq):
    a, x, b, y = Symbol(real=True)
    Eq << apply(Equal(a, x), x < b)
    
    Eq << Eq[2].subs(Eq[0])


if __name__ == '__main__':
    run()
# created on 2023-05-01
