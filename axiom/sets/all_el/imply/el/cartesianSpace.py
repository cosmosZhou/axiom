from util import *


@apply(simplify=False)
def apply(given):
    (e, S), *limits = given.of(All[Element])

    shape = []
    for limit in limits:
        x, a, b = limit
        assert a == 0
        assert x.is_integer
        assert e._has(x)
        shape.append(b)
    shape.reverse()
    return Element(Lamda(e, *limits).simplify(), CartesianSpace(S, *shape))


@prove
def prove(Eq):
    x = Symbol(integer=True, shape=(oo,))
    S = Symbol(etype=dtype.integer)
    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    Eq << apply(All[i:n](Element(x[i], S)))

    Eq << Eq[1].simplify()

    


if __name__ == '__main__':
    run()
# created on 2022-09-20
