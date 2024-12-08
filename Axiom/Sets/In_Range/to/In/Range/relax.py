from util import *


@apply
def apply(given, upper=None, lower=None):
    x, interval = given.of(Element)
    a, b = interval.of(Range)
    if upper is not None:
        assert upper >= b or upper - b >= 0
        b = upper
    elif lower is not None:
        assert lower <= a or lower - a <= 0
        a = lower

    return Element(x, Range(a, b))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x, a, b = Symbol(integer=True, given=True)
    Eq << apply(Element(x, Range(a, b)), upper=b + 1)

    Eq << Sets.In_Range.of.And.apply(Eq[1])

    Eq << Sets.In_Range.to.And.apply(Eq[0])

    Eq << Algebra.Lt.to.Lt.relax.apply(Eq[-1], upper=b + 1)




if __name__ == '__main__':
    run()
# created on 2023-08-20
