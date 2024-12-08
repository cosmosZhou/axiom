from util import *


@apply
def apply(given):
    A = given.of(Unequal[EmptySet])
    a, b = A.of(Range)
    return Greater(b, a)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    a, b = Symbol(integer=True, given=True)
    Eq << apply(Unequal(Range(a, b), a.emptySet))

    Eq << Sets.Ne_EmptySet.to.Any_In.apply(Eq[0])

    Eq << Eq[-1].this.expr.apply(Sets.In_Range.to.And)

    Eq << Eq[-1].this.expr.apply(Algebra.Lt.Ge.to.Gt.trans)


if __name__ == '__main__':
    run()
# created on 2018-10-18
