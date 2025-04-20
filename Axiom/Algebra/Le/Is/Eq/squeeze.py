from util import *


@apply
def apply(given):
    x, a = given.of(LessEqual)
    assert x >= a
    return Equal(x, a)


@prove
def prove(Eq):
    from Axiom import Algebra, Logic
    x = Symbol(domain=Interval(1, oo))

    Eq << apply(LessEqual(x, 1))

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[-1])

    Eq << Eq[-2].this.apply(Logic.Imp.Is.Or_Not)

    Eq << Eq[-1].apply(Algebra.Given.given.Or)


if __name__ == '__main__':
    run()

# created on 2019-11-26
