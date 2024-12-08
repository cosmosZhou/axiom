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
    from Axiom import Algebra, Sets

    k = Symbol(integer=True, positive=True)
    S = Symbol(etype=dtype.integer[k])
    Eq << apply(Equal(Card(S), 2))

    Eq << Algebra.Eq.to.Ge.apply(Eq[0])

    Eq << Sets.Ge.to.Any.Ne.apply(Eq[-1], *Eq[1].variables)

    Eq << Sets.Any.to.Any.limits.swap.apply(Eq[-1], simplify=False)

    Eq.S_supset = Eq[-1].this.expr.apply(Sets.In.In.to.Subset.FiniteSet, simplify=False)

    Eq << Eq.S_supset.this.expr.apply(Sets.Subset.to.Eq.Union, simplify=None, ret=0)

    Eq << Algebra.Any_And.to.Any.limits_absorb.apply(Eq[-1], index=1)

    Eq << Eq[-1].this.expr.apply(Sets.Eq.to.Eq.Card)

    Eq << Eq[-1].this.find(Card).apply(Sets.Card.eq.Add)


    Eq << Eq[-1].this.find(Piecewise).apply(Algebra.Piece.eq.Delta)
    Eq << Eq[-1].subs(Eq[0])
    Eq << Eq[-1].this.expr - 2
    Eq << Eq[-1].this.expr.apply(Algebra.Eq_0.to.Eq)
    Eq << Any(Unequal(Eq[-1].rhs, 0), *Eq.S_supset.limits, plausible=True)
    Eq << Eq[-1].this.expr.apply(Algebra.Ne_0.to.Eq.Delta)
    Eq << Algebra.Any.to.Any.And.limits.unleash.apply(Eq[-1])
    Eq << ~Eq[-2]
    Eq << Algebra.All.Any.to.Any.And.apply(Eq[-1], Eq[-4])
    Eq << Eq[-1].this.expr.apply(Algebra.Eq.Eq.to.Eq.trans)
    Eq << Eq[-1].this.expr.apply(Sets.Eq_0.to.Subset)
    Eq << Algebra.Any.to.Any.And.limits.unleash.apply(Eq[-1])
    Eq << Algebra.Any_And.to.Any.limits_absorb.apply(Eq[-1])
    Eq << Eq[-1].this.expr.apply(Sets.Subset.Subset.to.Eq.squeeze)




if __name__ == '__main__':
    run()

# created on 2020-09-07
# updated on 2023-06-01
