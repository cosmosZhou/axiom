from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(All[Subset])
    return Subset(Cup(lhs, *limits).simplify(), Cup(rhs, *limits).simplify())


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    f, g = Function(shape=(), etype=dtype.integer)
    Eq << apply(All[i:n](Subset(f(i), g(i))))

    Eq.hypothesis = Imply(Eq[0], Eq[1], plausible=True)

    Eq.initial = Eq.hypothesis.subs(n, 1)

    Eq.induct = Eq.hypothesis.subs(n, n + 1)

    Eq << Algebra.Imply.to.Imply.And.both_sided.apply(Eq.hypothesis, cond=Subset(f(n), g(n)))

    Eq << Eq[-1].this.rhs.apply(Sets.Subset.Subset.to.Subset.Cup.push)
    Eq << Eq[-1].this.lhs.apply(Algebra.Cond.All.of.All.push)

    Eq << Imply(Eq.hypothesis, Eq.induct, plausible=True)
    Eq << Algebra.Imply.to.Cond.induct.apply(Eq[-1], n=n, start=1)
    Eq << Algebra.Cond.Imply.to.Cond.trans.apply(Eq[0], Eq.hypothesis)





if __name__ == '__main__':
    run()

# created on 2020-08-03
# updated on 2023-05-21
from . import lhs