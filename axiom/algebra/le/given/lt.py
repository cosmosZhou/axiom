from util import *


@apply
def apply(given):
    x, a = given.of(LessEqual) 
    assert x.is_integer and a.is_integer
    return Less(x, a + 1)


@prove
def prove(Eq):
    x = Symbol.x(integer=True, given=True)
    a = Symbol.a(integer=True, given=True)

    Eq << apply(x <= a)

    Eq << ~Eq[0]

    Eq <<= Eq[-1] & Eq[1]


if __name__ == '__main__':
    run()
