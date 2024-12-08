from util import *


@apply
def apply(ge_a, ge_b):
    x, a = ge_a.of(GreaterEqual)
    S[x], b = ge_b.of(GreaterEqual)
    return x >= Max(a, b)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y, b = Symbol(real=True, given=True)
    Eq << apply(x >= y, x >= b)

    Eq << Algebra.Iff.of.And.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Ge.Ge.to.Ge.Max)

    Eq << Eq[-1].this.lhs.apply(Algebra.Ge.Ge.of.Ge.Max)




if __name__ == '__main__':
    run()
# created on 2022-01-03
# updated on 2023-05-21
