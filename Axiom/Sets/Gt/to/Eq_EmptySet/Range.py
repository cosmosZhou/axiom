from util import *


@apply
def apply(given):
    a, b = given.of(Greater)
    assert a.is_integer and b.is_integer
    return Equal(Range(a, b), a.emptySet)


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    x, y = Symbol(integer=True, given=True)
    Eq << apply(x > y)

    Eq << Algebra.Gt.to.Ge.relax.apply(Eq[0])
    Eq << Sets.Ge.to.Eq_EmptySet.Range.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-04-17