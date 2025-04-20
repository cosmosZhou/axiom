from util import *


@apply
def apply(self, old, new):
    from Axiom.Algebra.Sum.limits.subs.Neg import limits_subs
    return limits_subs(Any, self, old, new)


@prove
def prove(Eq):
    from Axiom import Algebra, Logic

    i, a, b, c = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Any[i:a:b](f(i)), i, c - i)

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Any.of.Any.limits.subs.Neg, i, c - i)
    Eq << Eq[-1].this.lhs.apply(Algebra.Any.of.Any.limits.subs.Neg, i, c - i)


if __name__ == '__main__':
    run()
# created on 2019-02-20
from . import real
