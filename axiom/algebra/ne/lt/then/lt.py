from util import *


@apply
def apply(ne, lt):
    x, a = ne.of(Unequal)
    S[x], S[a + 1] = lt.of(Less)
    assert x.is_integer and a.is_integer
    return x < a


@prove
def prove(Eq):
    from axiom import algebra

    a, x = Symbol(integer=True)
    Eq << apply(Unequal(x, a), x < a + 1)

    Eq << algebra.lt.then.le.strengthen.apply(Eq[1])

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()
# created on 2023-04-13
