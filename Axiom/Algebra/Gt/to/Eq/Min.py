from util import *


@apply
def apply(given, reverse=False):
    a, b = given.of(Greater)
    if reverse:
        return Equal(b, Min(a, b))
    return Equal(Min(a, b), b)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(x > y)

    Eq << Eq[-1].this.lhs.apply(Algebra.Min.eq.Piece)

    Eq << Eq[-1].this.lhs.apply(Algebra.Piece.swap)

    Eq << Algebra.Cond.Cond.of.And.subs.apply(Eq[0], Eq[-1])




if __name__ == '__main__':
    run()
# created on 2018-09-09
# updated on 2023-06-23