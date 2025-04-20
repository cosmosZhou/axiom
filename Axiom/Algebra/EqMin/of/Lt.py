from util import *


@apply
def apply(given, reverse=False):
    a, b = given.of(Less)
    if reverse:
        return Equal(a, Min(a, b))
    return Equal(Min(a, b), a)



@prove
def prove(Eq):
    from Axiom import Algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(x < y)

    Eq << Eq[-1].this.lhs.apply(Algebra.Min.eq.Ite.Lt)

    Eq << Algebra.Cond.Cond.given.And.subs.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-08-31
# updated on 2023-06-23
