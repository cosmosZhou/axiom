from util import *


@apply
def apply(given):
    A = given.of(Unequal[EmptySet])
    a, b = A.of(Range)
    return Greater(b, a)


@prove
def prove(Eq):
    from Axiom import Set, Algebra

    a, b = Symbol(integer=True, given=True)
    Eq << apply(Unequal(Range(a, b), a.emptySet))

    Eq << Set.Any_Mem.of.Ne_EmptySet.apply(Eq[0])

    Eq << Eq[-1].this.expr.apply(Set.And.of.Mem_Range)

    Eq << Eq[-1].this.expr.apply(Algebra.Gt.of.Lt.Ge)


if __name__ == '__main__':
    run()
# created on 2018-10-18
