from util import *


@apply
def apply(given):
    (fx, (x, S[1])), (S[x], domain) = given.of(All[Derivative >= 0])
    a, b = domain.of(Interval)
    assert not domain.left_open
    return All[x:Interval(a, b, right_open=domain.right_open)](GreaterEqual(fx, fx._subs(x, a)))


@prove
def prove(Eq):
    from Axiom import Algebra, Calculus, Sets

    a, b = Symbol(real=True, given=True)
    domain = Interval(a, b, right_open=True)
    x, t, e = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(All[x:domain](Derivative[x](f(x)) >= 0))

    Eq << Algebra.Cond.to.Imply.apply(Eq[0], cond=t < b)

    Eq << Algebra.Imply_And.to.Imply.And.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Lt.All.to.All.limits.restrict)

    Eq << Eq[-1].this.rhs.apply(Calculus.All_Ge_0.to.All.Ge.monotony.right_close)

    Eq << Eq[-1].subs(t, b - e)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << -Eq[-1].this.lhs

    Eq.suffice = Eq[-1].this.rhs.apply(Algebra.All.limits.subs.Neg.real, x, b - x)

    Eq << ~Eq[1]

    Eq << Eq[-1].this.apply(Algebra.Any.limits.subs.Neg.real, x, b - x)

    Eq << Algebra.Any.to.Any.And.limits.Cond.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Element).apply(Sets.In_Interval.to.Gt)

    η = Symbol(real=True, positive=True)
    Eq << Eq[-1].this.find(Greater).apply(Algebra.Gt_0.to.Any.Gt, var=η)

    Eq << Eq[-1].this.find(And).apply(Algebra.Cond.Any.to.Any.And, simplify=None)

    Eq << Algebra.Any.to.Any.limits.swap.apply(Eq[-1], simplify=None)

    Eq << Algebra.Any_And.to.Any.limits_absorb.apply(Eq[-1], 1)

    Eq << Eq.suffice.subs(e, η)

    Eq << Algebra.All.Any.to.Any.And.apply(Eq[-1], Eq[-2])




if __name__ == '__main__':
    run()
# created on 2023-10-03
