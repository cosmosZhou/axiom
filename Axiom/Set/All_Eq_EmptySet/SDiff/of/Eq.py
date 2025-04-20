from util import *


@apply
def apply(given, excludes=None):
    from sympy.concrete.limits import limits_dict

    (xi, *limits), (S[xi], *S[limits]) = given.of(Equal[Card[Cup], Sum[Card]])

    limitsDict = limits_dict(limits)
    i, *_ = limitsDict.keys()

    kwargs = i._assumptions.copy()
    if 'domain' in kwargs:
        del kwargs['domain']

    j = xi.generate_var(excludes=excludes, **kwargs)
    xj = xi.subs(i, j)

    i_domain = limitsDict[i] or i.domain

    limits = [(j, i_domain - {i})] + [*limits]
    return All(Equal(xi & xj, xi.etype.emptySet).simplify(), *limits)


@prove
def prove(Eq):
    from Axiom import Set, Algebra

    i = Symbol(integer=True)
    k = Symbol(integer=True, positive=True, given=True)
    x = Symbol(shape=(k + 1,), etype=dtype.integer, finiteset=True, given=True)
    Eq << apply(Equal(Card(Cup[i:k](x[i])), Sum[i:k](Card(x[i]))))

    j = Eq[-1].variables[0]
    Eq << ~Eq[-1]

    Eq << Eq[-1].this.expr.apply(Set.Gt_0.of.Ne_EmptySet)

    Eq << Set.CardUnion.eq.Sub_.AddCards.CardInter.principle.inclusion_exclusion.apply(x[i], x[j])

    Eq << Eq[-2].this.expr.apply(Algebra.Lt.of.Eq.Gt.subs, Eq[-1])

    Eq << Algebra.Any.And.of.Cond.Any.apply(Eq[0], Eq[-1], simplify=False)

    Eq.gt = Eq[-1].this.expr.apply(Algebra.GtSub.of.Eq.Lt)

    Eq << Eq[0].lhs.arg.this.apply(Set.Cup.eq.Union.split, cond={i, j})

    Eq.union_less_than = Set.CardCup.le.Sum_Card.apply(x[i], *Eq[-1].rhs.args[1].limits)

    Eq << Set.CardUnion.le.AddCardS.apply(*Eq[-1].rhs.args)

    Eq << Eq.gt.this.expr.apply(Algebra.Gt.of.Gt.Le.subs, Eq[-1])

    Eq << Eq[-1].this().expr.simplify()

    Eq << Eq[-1].this.find(Card + Card[~Cup]).apply(Set.Cup.eq.Union.doit.setlimit)

    Eq << Eq.union_less_than.this.find(Cup).limits_subs(Eq.union_less_than.find(Cup).variable, Eq[-1].find(Cup).variable)

    Eq << Eq[-1].this.expr.apply(Algebra.Gt.of.Gt.Le.subs, Eq.union_less_than)

    Eq << Eq[-1].this().expr.lhs.simplify()

    Eq << Algebra.Any.And.of.Any.limits.unleash.apply(Eq[-1], simplify=None)

    Eq << Algebra.Any.of.Any_And.limits_absorb.apply(Eq[-1], index=1, simplify=None)

    Eq << Eq[-1].this.find(Element).apply(Set.Ne.of.Mem)

    Eq << Eq[-1].this.expr.apply(Algebra.Cond.of.Ne.Cond.subs)





if __name__ == '__main__':
    run()

# created on 2020-07-18
# updated on 2023-05-20
