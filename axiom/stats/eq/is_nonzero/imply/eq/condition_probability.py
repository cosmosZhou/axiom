from util import *


@apply
def apply(equality, unequal):
    z, _y = unequal.of(Unequal[Probability[Conditioned], 0])

    (x, y), _x = equality.of(Equal[Conditioned])
    assert x == _x

    if _y != y:
        _y, z = z, _y

    assert _y == y

    return Equal(x | y & z, x | z)


@prove(proved=False)
def prove(Eq):
    x = Symbol.x(real=True, random=True)
    y = Symbol.y(real=True, random=True)
    z = Symbol.z(real=True, random=True)
    Eq << apply(Equal(x | y, x), Unequal(Probability(z | y), 0))


if __name__ == '__main__':
    run()
