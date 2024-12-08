from util import *


@apply
def apply(given):
    (fx, *limits), M = given.of(Less[Maxima])
    return All(fx < M, *limits)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, t = Symbol(real=True)
    M = Symbol(real=True, given=True)
    f = Function(real=True)
    S = Symbol(etype=dtype.real)
    Eq << apply(Maxima[x:S](f(x)) < M)

    Eq << Algebra.Lt.to.Le.relax.apply(Eq[0])

    Eq << Algebra.LeMaxima.to.All.Le.apply(Eq[-1])

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[1], cond=Equal(S, S.etype.emptySet))

    Eq << Algebra.Imply.of.Imply.subs.apply(Eq[-2])

    Eq << Eq[-1].this.rhs.expr.apply(Algebra.Lt.of.And)

    Eq << Eq[-1].this.rhs.apply(Algebra.All_And.of.And.All)

    Eq << Algebra.Imply.of.And.Imply.apply(Eq[-1])

    Eq << Algebra.Imply.of.Cond.apply(Eq[-1])

    Eq.infer_is_empty = Eq[-2].this.apply(Algebra.Imply.contraposition)

    Eq << Eq[0].this.lhs.limits_subs(x, t)

    Eq << Algebra.All_Le_Maxima.apply(Eq[0].lhs)

    Eq << Eq[-1].limits_subs(t, x)

    Eq << Algebra.Cond.Imply.of.And.Imply.And.apply(Eq[-1], Eq.infer_is_empty)

    Eq << Eq[-1].this.lhs.apply(Algebra.All.Any.to.Any.And)

    Eq << Eq[-1].this.lhs.expr.apply(Algebra.Eq.Le.to.Le.trans)

    Eq << Algebra.Cond.Imply.of.And.Imply.And.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-11-12
