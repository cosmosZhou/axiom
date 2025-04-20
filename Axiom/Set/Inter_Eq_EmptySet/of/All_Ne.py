from util import *


@apply
def apply(given):
    (xi, y), (i, S[0], n) = given.of(All[Unequal])
    if not xi._has(i):
        xi, y = y, xi

    x = Lamda[i:n](xi).simplify()

    return Equal({y} & x.cup_finiteset(), y.emptySet)


@prove
def prove(Eq):
    from Axiom import Set

    i = Symbol(integer=True)
    y = Symbol(real=True, given=True)
    x = Symbol(real=True, shape=(oo,), given=True)
    n = Symbol(integer=True, positive=True, given=True)
    Eq << apply(All[i:n](Unequal(x[i], y)))

    Eq << Set.Inter_Eq_EmptySet.given.NotMem.apply(Eq[1])

    Eq << Set.NotMem.given.All_NotMem.apply(Eq[-1])
    Eq << Eq[-1].this.expr.reversed


if __name__ == '__main__':
    run()
# created on 2019-02-03
