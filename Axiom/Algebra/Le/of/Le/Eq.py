from util import *


@apply
def apply(le, eq):
    from Axiom.Algebra.Lt.of.Lt.Eq import swap
    return LessEqual(*swap(LessEqual, le, eq))


@prove
def prove(Eq):
    from Axiom import Algebra

    a, x, b = Symbol(real=True)
    # Eq << apply(a <= x, Equal(b, a))
    # Eq << apply(a <= x, Equal(a, b))
    Eq << apply(a <= x, Equal(x, b))

    # Eq << apply(a <= x, Equal(b, x))
    Eq << Eq[0] + Eq[1]

    Eq << Eq[-1].this.apply(Algebra.Le.simp.terms.common)


if __name__ == '__main__':
    run()
# created on 2019-10-24

