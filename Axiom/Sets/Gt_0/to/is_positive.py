from util import *


@apply
def apply(given):
    x = given.of(Expr > 0)
    assert x.is_finite
    return Element(x, Interval.open(0, oo))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x = Symbol(complex=True)
    Eq << apply(x > 0)

    Eq << Sets.Gt.to.is_real.apply(Eq[0], simplify=None)

    Eq << Sets.In_Interval.to.Or.apply(Eq[-1], 0, left_open=True)

    Eq <<= Eq[0] & Eq[-1]

    Eq << Algebra.And.to.Or.apply(Eq[-1])

    Eq << Algebra.And.to.And.apply(Eq[-1], simplify=None)


if __name__ == '__main__':
    run()
# created on 2020-04-13
