from util import *


@apply
def apply(greater_than, _greater_than):
    a, x = greater_than.of(GreaterEqual)
    b, _x = _greater_than.of(LessEqual)
    if x != _x:
        a, x, S[x], b = _x, b, a, x,

    assert x.is_integer
    return Element(x, Range(b, a + 1))


@prove
def prove(Eq):
    from Axiom import Set, Algebra

    a, b, x = Symbol(integer=True, given=True)
    Eq << apply(x >= b, x <= a)

    # Eq << apply(b >= x, a <= x)
    Eq << Set.Mem_Range.given.And.apply(Eq[-1])



    Eq << Algebra.Lt.given.Le.strengthen.apply(Eq[-1])

    # Eq << Eq[-1].reversed
    # Eq << Eq[-2].reversed


if __name__ == '__main__':
    run()

# created on 2018-05-23
