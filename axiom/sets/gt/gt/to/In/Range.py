from util import *


@apply
def apply(greater_than, _greater_than):
    a, x = greater_than.of(Greater)
    _x, b = _greater_than.of(Greater)
    if x != _x:
        a, x, S[x], b = _x, b, a, x,

    assert x.is_integer
    return Element(x, Range(b + 1, a))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    a, b, x = Symbol(integer=True, given=True)
    # Eq << apply(x > b, a > x)
    Eq << apply(b > x, x > a)

    Eq << Sets.In_Range.of.And.apply(Eq[-1])

    Eq << Algebra.Ge.of.Gt.relax.apply(Eq[-2])

    Eq << Eq[-1].reversed

    # Eq << Eq[-2].reversed


if __name__ == '__main__':
    run()

# created on 2021-04-16
