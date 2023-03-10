from util import *


@apply
def apply(given, index=-1):
    eqs, q = given.of(Or >> Boolean)
    arr = tuple((Infer(eq, q) for eq in eqs))
    first = arr[:index]
    second = arr[index:]
    return And(*first), And(*second)


@prove
def prove(Eq):
    x, y, a, b = Symbol(integer=True)
    f, g = Function(integer=True)
    Eq << apply(Infer((x > b) | (x < a), f(x) > g(y)))

    Eq <<= Eq[1] & Eq[2]


if __name__ == '__main__':
    run()
# created on 2018-01-31
