from util import *


@apply
def apply(self, index=0, offset=None):
    from Axiom.Algebra.Sum.limits.subs.offset import limits_subs
    return limits_subs(All, self, index, offset)


@prove
def prove(Eq):
    from Axiom import Algebra, Set

    n, m = Symbol(integer=True)
    f = Function(integer=True)
    Eq << apply(All[n:1:m + 1](f(n) > 0), 1)

    Eq << Algebra.Or.of.All.subs.apply(Eq[0], n, n + 1)

    Eq << Eq[-1].this.args[1].apply(Set.NotMem.Sub.of.NotMem, 1)

    Eq << Algebra.All.of.Or.apply(Eq[-1], pivot=1, wrt=n)


if __name__ == '__main__':
    run()
# created on 2018-07-11
