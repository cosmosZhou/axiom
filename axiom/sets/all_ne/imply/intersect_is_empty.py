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
    from axiom import sets

    i = Symbol(integer=True)
    y = Symbol(real=True, given=True)
    x = Symbol(real=True, shape=(oo,), given=True)
    n = Symbol(integer=True, positive=True, given=True)
    Eq << apply(All[i:n](Unequal(x[i], y)))

    Eq << sets.intersect_is_empty.given.notin.apply(Eq[1])

    Eq << sets.notin.given.all_notin.apply(Eq[-1])
    Eq << Eq[-1].this.expr.reversed


if __name__ == '__main__':
    run()
# created on 2019-02-03
