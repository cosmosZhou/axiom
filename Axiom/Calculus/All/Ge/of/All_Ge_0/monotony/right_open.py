from util import *


@apply
def apply(given):
    (fx, (x, S[1])), (S[x], domain) = given.of(All[Derivative >= 0])
    a, b = domain.of(Interval)
    assert not domain.left_open
    return All[x:Interval(a, b, right_open=domain.right_open)](GreaterEqual(fx, fx._subs(x, a)))


@prove
def prove(Eq):
    from Axiom import Algebra, Calculus, Set, Logic

    a, b = Symbol(real=True, given=True)
    domain = Interval(a, b, right_open=True)
    x, t, e = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(All[x:domain](Derivative[x](f(x)) >= 0))

    Eq << Logic.Imp.of.Cond.apply(Eq[0], cond=t < b)

    Eq << Logic.Imp_And.of.ImpAnd.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.All.of.Lt.All.limits.restrict)

    Eq << Eq[-1].this.rhs.apply(Calculus.All.Ge.of.All_Ge_0.monotony.right_close)

    Eq << Eq[-1].subs(t, b - e)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << -Eq[-1].this.lhs

    Eq.suffice = Eq[-1].this.rhs.apply(Algebra.All.limits.subs.Neg.real, x, b - x)

    Eq << ~Eq[1]

    Eq << Eq[-1].this.apply(Algebra.Any.limits.subs.Neg.real, x, b - x)

    Eq << Algebra.Any.And.of.Any.limits.Cond.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Element).apply(Set.Gt.of.Mem_Icc)

    η = Symbol(real=True, positive=True)
    Eq << Eq[-1].this.find(Greater).apply(Algebra.Any.Gt.of.Gt_0, var=η)

    Eq << Eq[-1].this.find(And).apply(Algebra.Any.And.of.Cond.Any, simplify=None)

    Eq << Algebra.Any.of.Any.limits.swap.apply(Eq[-1], simplify=None)

    Eq << Algebra.Any.of.Any_And.limits_absorb.apply(Eq[-1], 1)

    Eq << Eq.suffice.subs(e, η)

    Eq << Algebra.Any.And.of.All.Any.apply(Eq[-1], Eq[-2])




if __name__ == '__main__':
    run()
# created on 2023-10-03
