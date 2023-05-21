from util import *


@apply
def apply(ne, lt):
    x, a = ne.of(Unequal)
    S[x], b = lt.of(Less)
    assert a <= b
    return x < a


@prove
def prove(Eq):
    from axiom import algebra

    a, x = Symbol(real=True)
    Eq << apply(Unequal(x, a), x < a + 1)

    Eq << algebra.lt.imply.ne.apply(Eq[2])

    Eq << algebra.lt.imply.lt.relax.apply(Eq[2], a + 1)

    


if __name__ == '__main__':
    run()
# created on 2023-04-13
