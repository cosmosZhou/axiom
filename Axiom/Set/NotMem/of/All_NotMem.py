from util import *


@apply
def apply(given):
    (e, S), *limits = given.of(All[NotElement])

    return NotElement(e, Cup(S, *limits))


@prove
def prove(Eq):
    from Axiom import Algebra, Logic

    n = Symbol(integer=True, positive=True)
    x, k = Symbol(integer=True)
    A = Symbol(shape=(oo,), etype=dtype.integer)
    Eq << apply(All[k:n](NotElement(x, A[k])))

    Eq.hypothesis = Imply(Eq[0], Eq[1], plausible=True)

    Eq.initial = Eq.hypothesis.subs(n, 1)

    Eq.induct = Eq.hypothesis.subs(n, n + 1)

    Eq << Logic.Imp.And.of.Imp.both_sided.apply(Eq.hypothesis, cond=NotElement(x, A[n]))
    Eq << Eq[-1].this.lhs.apply(Algebra.Cond.All.given.All.push)
    Eq << Imply(Eq.hypothesis, Eq.induct, plausible=True)
    Eq << Logic.Cond.of.Imp.induct.apply(Eq[-1], n=n, start=1)

    Eq << Logic.Cond.of.Imp.Cond.apply(Eq[0], Eq.hypothesis)





if __name__ == '__main__':
    run()

# created on 2018-09-08
# updated on 2023-05-21
