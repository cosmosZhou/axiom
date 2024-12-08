from util import *


@apply
def apply(given, upper=None, lower=None):
    x, interval = given.of(Element)
    (a, b), *shape = interval.of(CartesianSpace[Range])
    if upper is not None:
        assert upper >= b or upper - b >= 0
        b = upper
    elif lower is not None:
        assert lower <= a or lower - a <= 0
        a = lower

    return Element(x, CartesianSpace(Range(a, b), *shape))


@prove
def prove(Eq):
    from Axiom import Sets

    n = Symbol(integer=True, positive=True)
    a, b = Symbol(integer=True)
    x = Symbol(integer=True, shape=(n,))
    Eq << apply(Element(x, CartesianSpace(Range(a, b), n)), upper=b + 1)

    Eq << Sets.In_CartesianSpace.to.All.In.apply(Eq[0])

    Eq << Sets.In_CartesianSpace.of.All.In.apply(Eq[1])

    Eq << Sets.In_Range.of.In.Range.restrict.apply(Eq[-1], upper=b)



if __name__ == '__main__':
    run()
# created on 2023-08-20
