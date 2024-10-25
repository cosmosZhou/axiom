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

    Eq << algebra.eq.then.ge.apply(Eq[0])

    Eq << sets.ge.then.any.ne.apply(Eq[-1], *Eq[1].variables)

    Eq << sets.any.then.any.limits.swap.apply(Eq[-1], simplify=False)

    Eq.S_supset = Eq[-1].this.expr.apply(sets.el.el.then.subset.finiteset, simplify=False)

    Eq << Eq.S_supset.this.expr.apply(sets.subset.then.eq.union, simplify=None, ret=0)

    Eq << algebra.any_et.then.any.limits_absorb.apply(Eq[-1], index=1)

    Eq << Eq[-1].this.expr.apply(sets.eq.then.eq.card)

    Eq << Eq[-1].this.find(Card).apply(sets.card.to.add)


    Eq << Eq[-1].this.find(Piecewise).apply(algebra.piece.to.delta)
    Eq << Eq[-1].subs(Eq[0])
    Eq << Eq[-1].this.expr - 2
    Eq << Eq[-1].this.expr.apply(algebra.is_zero.then.eq)
    Eq << Any(Unequal(Eq[-1].rhs, 0), *Eq.S_supset.limits, plausible=True)
    Eq << Eq[-1].this.expr.apply(algebra.ne_zero.then.eq.delta)
    Eq << algebra.any.then.any.et.limits.unleash.apply(Eq[-1])
    Eq << ~Eq[-2]
    Eq << algebra.all.any.then.any.et.apply(Eq[-1], Eq[-4])
    Eq << Eq[-1].this.expr.apply(algebra.eq.eq.then.eq.trans)
    Eq << Eq[-1].this.expr.apply(sets.is_zero.then.subset)
    Eq << algebra.any.then.any.et.limits.unleash.apply(Eq[-1])
    Eq << algebra.any_et.then.any.limits_absorb.apply(Eq[-1])
    Eq << Eq[-1].this.expr.apply(sets.subset.subset.then.eq.squeeze)




if __name__ == '__main__':
    run()

# created on 2020-09-07
# updated on 2023-06-01
