from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(All[Subset])
    return Subset(Cup(lhs, *limits).simplify(), Cup(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import algebra, sets

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    f, g = Function(shape=(), etype=dtype.integer)
    Eq << apply(All[i:n](Subset(f(i), g(i))))

    Eq.hypothesis = Infer(Eq[0], Eq[1], plausible=True)

    Eq.initial = Eq.hypothesis.subs(n, 1)

    Eq.induct = Eq.hypothesis.subs(n, n + 1)

    Eq << algebra.infer.imply.infer.et.both_sided.apply(Eq.hypothesis, cond=Subset(f(n), g(n)))

    Eq << Eq[-1].this.rhs.apply(sets.subset.subset.imply.subset.cup.push)
    Eq << Eq[-1].this.lhs.apply(algebra.cond.all.given.all.push)
    
    Eq << Infer(Eq.hypothesis, Eq.induct, plausible=True)
    Eq << algebra.infer.imply.cond.induct.apply(Eq[-1], n=n, start=1)
    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[0], Eq.hypothesis)

    
    


if __name__ == '__main__':
    run()

from . import lhs
# created on 2020-08-03
# updated on 2023-05-21
