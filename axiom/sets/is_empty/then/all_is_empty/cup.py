from util import *


@apply
def apply(given):
    x_union = given.of(Equal[EmptySet])

    expr, *limits = x_union.of(Cup)
    return All(Equal(expr, x_union.etype.emptySet), *limits)


@prove
def prove(Eq):
    from axiom import sets, algebra

    i = Symbol(integer=True)
    k = Symbol(integer=True, positive=True, given=True)
    x = Symbol(shape=(k + 1,), etype=dtype.integer, given=True)
    Eq << apply(Equal(Cup[i:k + 1](x[i]), x[i].etype.emptySet))

    j = Symbol(domain=Range(k + 1))
    Eq << Eq[-1].limits_subs(i, j)

    Eq.paradox = ~Eq[-1]



    Eq << Eq[0].apply(sets.eq.then.eq.card)

    Eq << Eq[-1].this.lhs.apply(sets.card.to.add.split, x[j])

    Eq << sets.eq.then.eq.complement.apply(Eq[0], Eq.paradox.lhs)

    Eq << Eq[-1].apply(sets.eq.then.eq.card)

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Subset(*Eq[-1].lhs.arg.args, plausible=True)

    Eq << sets.subset_cup.of.any.subset.apply(Eq[-1])

    Eq << algebra.any.of.cond.subs.apply(Eq[-1], i, j)

    Eq << sets.subset.then.eq.intersect.apply(Eq[-2])

    Eq << Eq[-4].subs(Eq[-1])

    Eq << Eq.paradox.this.expr.apply(sets.ne_empty.then.gt_zero)
    Eq << algebra.cond.any.then.any.et.apply(Eq[-1], Eq[-2])





if __name__ == '__main__':
    run()

# created on 2020-08-09
# updated on 2023-06-01
