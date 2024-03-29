from util import *


@apply
def apply(all_is_complex):
    (expr, C), *limits = all_is_complex.of(All[Element])
    assert C in S.Complexes
    for limit in limits:
        x, domain = limit.coerce_setlimit()
        assert domain.is_finiteset

    return Element(Sum(expr, *limits), S.Complexes)


@prove
def prove(Eq):
    from axiom import algebra, sets

    x = Symbol(super_complex=True, shape=(oo,))
    i = Symbol(integer=True)
    n = Symbol(integer=True, given=False, nonnegative=True)
    Eq << apply(All[i:n](Element(x[i], S.Complexes)))

    Eq << Infer(Eq[0], Eq[1], plausible=True)

    Eq.induct = Eq[2].subs(n, n + 1)

    Eq << algebra.infer.imply.infer.et.both_sided.apply(Eq[2], cond=Element(x[n], S.Complexes))

    Eq << Eq[-1].this.lhs.apply(algebra.cond.all.given.all.push)

    Eq << Eq[-1].this.rhs.apply(sets.is_complex.is_complex.imply.is_complex.add)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.to.sub.push)

    Eq << Infer(Eq[2], Eq.induct, plausible=True)

    Eq << algebra.infer.imply.cond.induct.apply(Eq[-1], n=n, start=0)

    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[0], Eq[2])





if __name__ == '__main__':
    run()
# created on 2023-05-03
# updated on 2023-05-20
