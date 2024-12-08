from util import *


@apply
def apply(given):
    S_abs, positive = given.of(GreaterEqual)
    assert positive.is_extended_positive
    S = S_abs.of(Card)

    x = S.element_symbol()
    return Any[x](Element(x, S))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra
    S = Symbol(etype=dtype.integer, given=True)

    Eq << apply(Card(S) >= 1)

    Eq << Algebra.Ge.to.Gt.relax.apply(Eq[0], 0)

    Eq << Sets.Gt_0.to.Any_In.apply(Eq[-1], simplify=False)


if __name__ == '__main__':
    run()

# created on 2020-07-13
