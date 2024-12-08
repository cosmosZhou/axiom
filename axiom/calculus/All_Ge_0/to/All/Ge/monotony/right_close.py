from util import *


@apply
def apply(given):
    (fx, (x, S[1])), (S[x], domain) = given.of(All[Derivative >= 0])
    a, b = domain.of(Interval)
    assert domain.is_closed
    return All[x:Interval(a, b)](GreaterEqual(fx, fx._subs(x, a)))


@prove
def prove(Eq):
    from Axiom import Algebra, Sets, Calculus

    a, b, x = Symbol(real=True)
    domain = Interval(a, b)
    f = Function(real=True)
    Eq << apply(All[x:domain](Derivative[x](f(x)) >= 0))

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[1], cond=a < b)

    Eq << Eq[-1].this.rhs.apply(Algebra.All.of.Imply)

    Eq << Eq[-1].this.apply(Algebra.Imply.flatten)

    Eq << Eq[-1].this.lhs.apply(Sets.Ge.In.to.Eq)

    Eq << Algebra.Imply.of.Imply.subs.apply(Eq[-1])

    Eq << Algebra.Cond.to.Imply.apply(Eq[0], cond=a < b)

    Eq << Algebra.Imply_And.to.Imply.And.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Calculus.Lt.All_Ge_0.to.All.Ge.monotony.right_close)




if __name__ == '__main__':
    run()
# created on 2023-10-03
