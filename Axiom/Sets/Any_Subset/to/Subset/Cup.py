from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(Any[Subset])
    variables = [v for v, *_ in limits]
    assert not lhs.has(*variables)
    return Subset(lhs, Cup(rhs, *limits).simplify())


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    g = Function(shape=(), etype=dtype.integer)
    A = Symbol(etype=dtype.integer)
    Eq << apply(Any[i:n](Subset(A, g(i))))

    Eq << All[i:n](Subset(g(i), Cup[i:n](g(i))), plausible=True)

    Eq << Eq[-1].this.find(Cup).apply(Sets.Cup.eq.Union.split, cond={i})

    Eq << Eq[-1].this.expr.apply(Sets.Subset_union.of.Supset, 0)

    Eq << Eq[-1].this().find(Intersection).simplify()

    Eq << Eq[2].this.expr.apply(Sets.Subset.to.Eq.Union)

    Eq << Eq[0].this.expr.apply(Sets.Subset.to.Subset.Union.rhs, Eq[1].find(Cup))

    Eq << Algebra.All.Any.to.Any.And.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.expr.apply(Algebra.Eq.Cond.to.Cond.subs)


if __name__ == '__main__':
    run()
# created on 2023-06-01
