from util import *


@apply
def apply(given):
    (x, a), (S[x], b) = given.of(GreaterEqual | GreaterEqual)
    return GreaterEqual(x, Min(a, b))


@prove
def prove(Eq):
    from Axiom import Algebra

    x, a, b = Symbol(real=True, given=True)
    Eq << apply(GreaterEqual(x, a) | GreaterEqual(x, b))

    Eq << Algebra.Iff.of.And.apply(Eq[0])

    Eq << Eq[-1].this.rhs.apply(Algebra.Ge_Min.to.Or.Ge)

    Eq << Eq[-2].this.rhs.apply(Algebra.Ge_Min.of.Or.Ge)


if __name__ == '__main__':
    run()
# created on 2022-01-02
