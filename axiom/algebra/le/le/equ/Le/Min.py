from util import *


@apply
def apply(le_a, le_b):
    x, a = le_a.of(LessEqual)
    S[x], b = le_b.of(LessEqual)
    return x <= Min(a, b)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y, b = Symbol(real=True, given=True)
    Eq << apply(x <= y, x <= b)

    Eq << Algebra.Iff.of.And.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Le.Le.to.Le.Min)

    Eq << Eq[-1].this.lhs.apply(Algebra.Le.Le.of.Le.Min)




if __name__ == '__main__':
    run()
# created on 2022-01-03
# updated on 2023-05-21
