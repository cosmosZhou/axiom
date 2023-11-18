from util import *


@apply
def apply(given, *limits):
    e, s = given.of(Element)

    shape = []
    for limit in limits:
        x, S[0], b = limit
        assert x.is_integer
        assert e._has(x)
        shape.append(b)
    shape.reverse()
    return Element(Lamda(e, *limits).simplify(), CartesianSpace(s, *shape), evaluate=False)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(integer=True, shape=(oo,))
    S = Symbol(etype=dtype.integer)
    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    Eq << apply(Element(x[i], S), (i, 0, n))

    Eq << sets.el_cartesianSpace.given.all.el.apply(Eq[1])


    Eq << algebra.cond.imply.all.restrict.apply(Eq[0], (i, 0, n))





if __name__ == '__main__':
    run()

# created on 2021-03-03
# updated on 2023-07-02
