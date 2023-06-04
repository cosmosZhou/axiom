from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(Any[Subset])
    variables = [v for v, *_ in limits]
    assert not lhs.has(*variables)
    return Subset(lhs, Cup(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import sets, algebra

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    g = Function(shape=(), etype=dtype.integer)
    A = Symbol(etype=dtype.integer)
    Eq << apply(Any[i:n](Subset(A, g(i))))

    Eq << All[i:n](Subset(g(i), Cup[i:n](g(i))), plausible=True)

    Eq << Eq[-1].this.find(Cup).apply(sets.cup.to.union.split, cond={i})

    Eq << Eq[-1].this.expr.apply(sets.subset_union.given.supset, 0)

    Eq << Eq[-1].this().find(Intersection).simplify()

    Eq << Eq[2].this.expr.apply(sets.subset.imply.eq.union)

    Eq << Eq[0].this.expr.apply(sets.subset.imply.subset.union.rhs, Eq[1].find(Cup))

    Eq << algebra.all.any.imply.any_et.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.expr.apply(algebra.eq.cond.imply.cond.subs)


if __name__ == '__main__':
    run()
# created on 2023-06-01
