from util import *


@apply
def apply(greater_than, strict_greater_than):
    a, x = greater_than.of(GreaterEqual)
    _x, b = strict_greater_than.of(Greater)
    if x != _x:
        a, x, S[x], b = _x, b, a, x,
    else:
        a += 1
        b += 1

    assert x.is_integer
    return Element(x, Range(b, a))


@prove
def prove(Eq):
    from Axiom import Set, Algebra

    a, b, x = Symbol(integer=True, given=True)
    # Eq << apply(x >= b, a > x)
    Eq << apply(b >= x, x > a)

    Eq << Set.Mem_Range.given.And.apply(Eq[-1])

    Eq << Algebra.Ge.given.Gt.relax.apply(Eq[-2])

    Eq << Algebra.Lt.given.Le.strengthen.apply(Eq[-1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()



# created on 2021-04-09
