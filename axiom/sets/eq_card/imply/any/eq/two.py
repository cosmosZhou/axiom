from util import *


@apply
def apply(given, x=None, y=None):
    S = given.of(Equal[Card, 2])

    if x is None:
        x = S.generate_var(**S.etype.dict)
    if y is None:
        y = S.generate_var(excludes={x}, **S.etype.dict)
    return Any[x: Unequal(x, y), y](Equal(S, {x, y}))


@prove
def prove(Eq):
    from axiom import algebra, sets

    k = Symbol(integer=True, positive=True)
    S = Symbol(etype=dtype.integer[k])
    Eq << apply(Equal(Card(S), 2))

    Eq << algebra.eq.imply.ge.apply(Eq[0])

    Eq << sets.ge.imply.any.ne.apply(Eq[-1], *Eq[1].variables)

    Eq << sets.any.imply.any.limits.swap.apply(Eq[-1], simplify=False)

    Eq.S_supset = Eq[-1].this.expr.apply(sets.el.el.imply.subset.finiteset, simplify=False)

    Eq << Eq.S_supset.this.expr.apply(sets.subset.imply.eq.union, simplify=None, ret=0)

    Eq << algebra.any_et.imply.any.limits_absorb.apply(Eq[-1], index=1)

    Eq << Eq[-1].this.expr.apply(sets.eq.imply.eq.card)

    Eq << Eq[-1].this.find(Card).apply(sets.card.to.add)


    Eq << Eq[-1].this.find(Piecewise).apply(algebra.piece.to.delta)
    Eq << Eq[-1].subs(Eq[0])
    Eq << Eq[-1].this.expr - 2
    Eq << Eq[-1].this.expr.apply(algebra.is_zero.imply.eq)
    Eq << Any(Unequal(Eq[-1].rhs, 0), *Eq.S_supset.limits, plausible=True)
    Eq << Eq[-1].this.expr.apply(algebra.ne_zero.imply.eq.delta)
    Eq << algebra.any.imply.any.et.limits.unleash.apply(Eq[-1])
    Eq << ~Eq[-2]
    Eq << algebra.all.any.imply.any.et.apply(Eq[-1], Eq[-4])
    Eq << Eq[-1].this.expr.apply(algebra.eq.eq.imply.eq.transit)
    Eq << Eq[-1].this.expr.apply(sets.is_zero.imply.subset)
    Eq << algebra.any.imply.any.et.limits.unleash.apply(Eq[-1])
    Eq << algebra.any_et.imply.any.limits_absorb.apply(Eq[-1])
    Eq << Eq[-1].this.expr.apply(sets.subset.subset.imply.eq.squeeze)




if __name__ == '__main__':
    run()

# created on 2020-09-07
# updated on 2023-06-01