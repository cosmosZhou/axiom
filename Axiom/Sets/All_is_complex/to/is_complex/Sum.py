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
    from Axiom import Algebra, Sets

    x = Symbol(super_complex=True, shape=(oo,))
    i = Symbol(integer=True)
    n = Symbol(integer=True, given=False, nonnegative=True)
    Eq << apply(All[i:n](Element(x[i], S.Complexes)))

    Eq << Imply(Eq[0], Eq[1], plausible=True)

    Eq.induct = Eq[2].subs(n, n + 1)

    Eq << Algebra.Imply.to.Imply.And.both_sided.apply(Eq[2], cond=Element(x[n], S.Complexes))

    Eq << Eq[-1].this.lhs.apply(Algebra.Cond.All.of.All.push)

    Eq << Eq[-1].this.rhs.apply(Sets.is_complex.is_complex.to.is_complex.Add)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.eq.Sub.push)

    Eq << Imply(Eq[2], Eq.induct, plausible=True)

    Eq << Algebra.Imply.to.Cond.induct.apply(Eq[-1], n=n, start=0)

    Eq << Algebra.Cond.Imply.to.Cond.trans.apply(Eq[0], Eq[2])





if __name__ == '__main__':
    run()
# created on 2023-05-03
# updated on 2023-05-20
