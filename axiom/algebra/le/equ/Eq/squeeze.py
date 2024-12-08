from util import *


@apply
def apply(given):
    x, a = given.of(LessEqual)
    assert x >= a
    return Equal(x, a)


@prove
def prove(Eq):
    from Axiom import Algebra
    x = Symbol(domain=Interval(1, oo))

    Eq << apply(LessEqual(x, 1))

    Eq << Algebra.Iff.of.And.apply(Eq[-1])

    Eq << Eq[-2].this.apply(Algebra.Imply.equ.Or)

    Eq << Eq[-1].apply(Algebra.Given.of.Or)


if __name__ == '__main__':
    run()

# created on 2019-11-26
