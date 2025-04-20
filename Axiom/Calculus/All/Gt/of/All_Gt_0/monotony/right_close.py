from util import *


@apply
def apply(given):
    (fx, (x, S[1])), (S[x], domain) = given.of(All[Derivative > 0])
    a, b = domain.of(Interval)
    assert domain.is_closed
    return All[x:Interval(a, b, left_open=True)](Greater(fx, fx._subs(x, a)))


@prove
def prove(Eq):
    from Axiom import Algebra, Set, Calculus, Logic

    a, b, x = Symbol(real=True)
    domain = Interval(a, b)
    f = Function(real=True)
    Eq << apply(All[x:domain](Derivative[x](f(x)) > 0))

    Eq << Logic.Cond.given.And.Imp.split.apply(Eq[1], cond=a < b)

    Eq << Eq[-1].this.rhs.apply(Algebra.All.given.All.And.limits_cond, simplify=None)

    Eq << (a >= b).this.apply(Set.Eq_EmptySet.Icc.of.Ge, left_open=True)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.Cond.given.And.subs)

    Eq << Logic.Imp.of.Cond.apply(Eq[0], cond=a < b)

    Eq << Logic.Imp_And.of.ImpAnd.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Calculus.All.Gt.of.Lt.All_Gt_0.monotony.right_close)




if __name__ == '__main__':
    run()
# created on 2020-04-23
# updated on 2023-08-26
