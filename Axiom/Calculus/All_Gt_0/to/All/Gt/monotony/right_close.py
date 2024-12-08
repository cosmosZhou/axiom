from util import *


@apply
def apply(given):
    (fx, (x, S[1])), (S[x], domain) = given.of(All[Derivative > 0])
    a, b = domain.of(Interval)
    assert domain.is_closed
    return All[x:Interval(a, b, left_open=True)](Greater(fx, fx._subs(x, a)))


@prove
def prove(Eq):
    from Axiom import Algebra, Sets, Calculus

    a, b, x = Symbol(real=True)
    domain = Interval(a, b)
    f = Function(real=True)
    Eq << apply(All[x:domain](Derivative[x](f(x)) > 0))

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[1], cond=a < b)

    Eq << Eq[-1].this.rhs.apply(Algebra.All.of.All.And.limits_cond, simplify=None)

    Eq << (a >= b).this.apply(Sets.Ge.to.Eq_EmptySet.Interval, left_open=True)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.Cond.of.And.subs)

    Eq << Algebra.Cond.to.Imply.apply(Eq[0], cond=a < b)

    Eq << Algebra.Imply_And.to.Imply.And.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Calculus.Lt.All_Gt_0.to.All.Gt.monotony.right_close)




if __name__ == '__main__':
    run()
# created on 2020-04-23
# updated on 2023-08-26
