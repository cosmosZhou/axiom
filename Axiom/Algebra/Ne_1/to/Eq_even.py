from util import *


@apply
def apply(given):
    n = given.of(Unequal[Expr % 2, 1])
    return Equal(n % 2, 0)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra
    n = Symbol(integer=True)

    Eq << apply(Unequal(n % 2, 1))

    Eq << Sets.Mod.el.Range.apply(n % 2)

    Eq << Sets.In_Range.to.Or.apply(Eq[-1])

    Eq << Algebra.Cond.Or.to.Cond.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-05-22
