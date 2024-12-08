from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(All[GreaterEqual])
    assert Tuple.is_nonemptyset(limits)
    return GreaterEqual(Minima(lhs, *limits).simplify(), Minima(rhs, *limits).simplify())


@prove
def prove(Eq):
    from Axiom import Algebra

    n = Symbol(integer=True, positive=True, given=False)
    i = Symbol(integer=True)
    f, g = Function(shape=(), real=True)
    Eq << apply(All[i:n](GreaterEqual(f(i), g(i))))

    n = Symbol(integer=True, positive=True, given=False)
    i = Symbol(integer=True)
    f, g = Function(shape=(), real=True)
    Eq << apply(All[i:n](GreaterEqual(f(i), g(i))))

    Eq << Imply(Eq[0], Eq[1], plausible=True)

    Eq.induct = Eq[2].subs(n, n + 1)

    Eq << Eq.induct.this.find(Minima).apply(Algebra.Minima.eq.Min.pop)

    Eq << Eq[-1].this.find(GreaterEqual[~Minima]).apply(Algebra.Minima.eq.Min.pop)

    Eq << Algebra.Imply.to.Imply.And.both_sided.apply(Eq[2], cond=f(n) >= g(n))

    Eq << Eq[-1].this.lhs.apply(Algebra.Cond.All.of.All.push)

    Eq << Eq[-1].this.rhs.apply(Algebra.Ge.Ge.to.Ge.Min)

    Eq << Imply(Eq[2], Eq.induct, plausible=True)

    Eq << Algebra.Imply.to.Cond.induct.apply(Eq[-1], n=n, start=1)

    Eq << Algebra.Cond.Imply.to.Cond.trans.apply(Eq[0], Eq[2])


if __name__ == '__main__':
    run()
# created on 2023-04-23
