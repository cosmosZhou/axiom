from util import *


@apply
def apply(given):
    n, b = given.of(LessEqual)
    assert n.is_finite
    return Element(n, Interval(-oo, oo))


@prove
def prove(Eq):
    from Axiom import Sets

    x = Symbol(complex=True, given=True)
    b = Symbol(real=True, given=True)
    Eq << apply(x <= b)

    Eq << Sets.Le.to.In.Interval.apply(Eq[0])

    Eq << Sets.In.to.In.relax.apply(Eq[-1], Interval(-oo, oo), simplify=None)


if __name__ == '__main__':
    run()
# created on 2021-02-15
