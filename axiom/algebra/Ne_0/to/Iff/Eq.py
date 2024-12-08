from util import *


@apply
def apply(given, x):
    p = given.of(Unequal[0])
    return Iff(Equal(x, 0), Equal(x * p, 0))


@prove
def prove(Eq):
    from Axiom import Algebra

    p, x = Symbol(complex=True)
    Eq << apply(Unequal(p, 0), x)

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[1])

    Eq << Eq[-2].this.lhs * p

    Eq << Eq[-1].this.lhs / p

    Eq << Algebra.Cond.of.Cond.subs.Bool.apply(Eq[-1], cond=Eq[0], invert=True)


if __name__ == '__main__':
    run()
# created on 2018-11-09
