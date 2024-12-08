from util import *


@apply
def apply(given):
    (xi, limit), (S[xi], S[limit]) = given.of(Equal[Card[Cup], Sum[Card]])

    i, S[0], n = limit

    j = xi.generate_var(integer=True)
    xj = xi.subs(i, j)

    return All[j:i, i:n](Equal(xi & xj, xi.etype.emptySet))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=True)
    x = Symbol(shape=(oo,), etype=dtype.integer, finiteset=True, given=True)
    Eq << apply(Equal(Card(Cup[i:n](x[i])), Sum[i:n](Card(x[i]))))

    j = Eq[-1].variables[0]
    Eq << ~Eq[-1]

    Eq << Eq[-1].this.expr.apply(Sets.Ne_EmptySet.to.Gt_0)

    Eq << Sets.CardUnion.eq.Sub_.AddCards.CardIntersect.principle.inclusion_exclusion.apply(x[i], x[j])

    Eq << Eq[-2].this.expr.apply(Algebra.Eq.Gt.to.Lt.subs, Eq[-1])

    Eq << Algebra.Cond.Any.to.Any.And.apply(Eq[0], Eq[-1], simplify=False)

    Eq.gt = Eq[-1].this.expr.apply(Algebra.Eq.Lt.to.Gt.Sub)

    Eq << Eq[0].lhs.arg.this.apply(Sets.Cup.eq.Union.split, cond={i, j})

    Eq.union_less_than = Sets.CardCup.le.Sum_Card.apply(x[i], *Eq[-1].rhs.args[1].limits)

    Eq << Sets.CardUnion.le.AddCardS.apply(*Eq[-1].rhs.args)

    Eq << Eq.gt.this.expr.apply(Algebra.Gt.Le.to.Gt.subs, Eq[-1])

    Eq << Eq[-1].this().find(Intersection).simplify()

    Eq << Eq[-1].this.find(Cup).apply(Sets.Cup.eq.Union.doit.setlimit)

    Eq << Eq.union_less_than.this.find(Cup).limits_subs(Eq.union_less_than.find(Cup).variable, Eq[-1].find(Cup).variable)

    Eq << Eq[-1].this.expr.apply(Algebra.Gt.Le.to.Gt.subs, Eq.union_less_than)

    Eq << Eq[-1].this().expr.lhs.simplify()


if __name__ == '__main__':
    run()


# created on 2021-03-19
# updated on 2023-05-18

del Complement
from . import Complement
