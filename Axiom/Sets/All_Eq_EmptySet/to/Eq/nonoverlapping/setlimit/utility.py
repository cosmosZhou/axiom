from util import *


@apply
def apply(given):
    (xi, xj), *limits = given.of(All[Equal[Intersection, EmptySet]])
    * limits, (_, j_domain) = limits
    n_Interval, i = j_domain.of(Complement)
    n = n_Interval.stop
    i, *_ = i.args

    if not xi.has(i):
        xi = xj
        assert xj.has(i)

    eq = Equal(Card(Cup[i:n](xi)), Sum[i:n](Card(xi)))
    if limits:
        return All(eq, *limits)
    else:
        return eq


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    i, j = Symbol(integer=True)
    n = Symbol(domain=Range(2, oo), given=False)
    x = Symbol(shape=(oo,), etype=dtype.integer, finiteset=True)
    i_domain = Range(n)
    Eq << apply(All(Equal(x[i] & x[j], x[i].etype.emptySet), (j, i_domain - {i})))

    Eq.initial = Eq[-1].subs(n, 2)

    Eq << Eq.initial.this.lhs.doit()

    Eq << Eq[-1].this.rhs.doit()

    Eq << Eq[0].subs(i, 1)

    Eq << Algebra.All.to.Cond.subs.apply(Eq[-1], j, 0)

    Eq << Sets.CardUnion.eq.Sub_.AddCards.CardIntersect.principle.inclusion_exclusion.apply(*Eq[-1].lhs.args).subs(Eq[-1])

    Eq.induct = Eq[1].subs(n, n + 1)

    Eq << Eq.induct.lhs.arg.this.apply(Sets.Cup.eq.Union.split, cond={n})

    Eq << Sets.CardUnion.eq.Sub_.AddCards.CardIntersect.principle.inclusion_exclusion.apply(*Eq[-1].rhs.args)

    Eq << Eq[0].subs(i, n).limits_subs(j, i)

    Eq << Sets.All_Eq.to.Eq.Cup.apply(Eq[-1])

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Eq[-1].subs(Eq[1])

    Eq << Eq.induct.rhs.this.apply(Algebra.Sum.eq.Add.split, cond={n})

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Imply(Eq[1], Eq.induct, plausible=True)

    Eq << Algebra.Cond.Imply.to.Cond.induct.apply(Eq.initial, Eq[-1], n=n, start=2)


if __name__ == '__main__':
    run()

# created on 2020-08-05
