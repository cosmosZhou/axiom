from util import *


@apply
def apply(all_is_real):
    (expr, C), *limits = all_is_real.of(All[Element])
    assert C in Reals
    for limit in limits:
        x, domain = limit.coerce_setlimit()
        assert domain.is_finiteset

    return Element(Sum(expr, *limits), Reals)


@prove
def prove(Eq):
    from Axiom import Algebra, Set, Logic

    x = Symbol(super_complex=True, shape=(oo,))
    i = Symbol(integer=True)
    n = Symbol(integer=True, given=False, nonnegative=True)
    Eq << apply(All[i:n](Element(x[i], Reals)))

    Eq << Imply(Eq[0], Eq[1], plausible=True)

    Eq.induct = Eq[2].subs(n, n + 1)

    Eq << Logic.Imp.And.of.Imp.both_sided.apply(Eq[2], cond=Element(x[n], Reals))

    Eq << Eq[-1].this.lhs.apply(Algebra.Cond.All.given.All.push)

    Eq << Eq[-1].this.rhs.apply(Set.IsReal.Add.of.IsReal.IsReal)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.eq.Sub.push)
    Eq << Imply(Eq[2], Eq.induct, plausible=True)

    Eq << Logic.Cond.of.Imp.induct.apply(Eq[-1], n=n, start=0)

    Eq << Logic.Cond.of.Imp.Cond.apply(Eq[0], Eq[2])




if __name__ == '__main__':
    run()
# created on 2023-05-03
# updated on 2023-05-20
