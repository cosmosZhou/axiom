from util import *


@apply
def apply(el, is_finite):
    λ, domain = el.of(Element)
    S[0], S[1] = domain.of(Interval)
    assert domain.right_open and domain.left_open

    fn, (n, *cond) = is_finite.of(Sup[Abs] < Infinity)
    if cond:
        S[0], S[oo] = cond
    assert n.is_integer
    return Equal(Limit[n:oo](λ ** n * fn), ZeroMatrix(*fn.shape))


@prove
def prove(Eq):
    from Axiom import Algebra, Sets, Calculus

    x = Symbol(real=True, shape=(oo,))
    γ = Symbol(real=True)
    n = Symbol(integer=True)
    Eq << apply(Element(γ, Interval(0, 1, left_open=True, right_open=True)), Less(Sup[n:oo](Abs(x[n])), oo))

    Eq << Algebra.All_Le_Sup.apply(Eq[1].find(Sup))

    Eq.gt_zero, Eq.lt = Sets.In_Interval.to.And.apply(Eq[0])

    Eq << Algebra.Gt_0.to.Gt_0.Pow.apply(Eq.gt_zero, n)

    Eq << Algebra.Gt_0.to.Gt_0.Abs.apply(Eq[-1])

    Eq << Algebra.Gt_0.Le.to.Le.Mul.apply(Eq[-1], Eq[-3])

    Eq <<  Calculus.Le.to.Le.Limit.apply(Eq[-1], (n, oo))

    Eq.le = Eq[-1].this.rhs.apply(Calculus.Limit.eq.Mul)

    Eq << Calculus.In_Interval.to.Eq_0.Limit.geometric_series.positive.apply(Eq[0], n)

    Eq << Sets.Eq_0.to.is_real.apply(Eq[-1])

    Eq << Calculus.is_limited.to.Eq.Abs.Limit.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[-3])

    Eq << Eq.le.subs(Eq[-1])

    Eq << Eq[-1].this.find(Mul).apply(Algebra.Mul.eq.Abs)

    Eq << GreaterEqual(Eq[-1].lhs.expr, 0, plausible=True)

    Eq << Calculus.Ge.to.Ge.Limit.apply(Eq[-1], (n, oo))

    Eq << Algebra.Ge.Le.to.Eq.apply(Eq[-1], Eq[-3])

    Eq << Calculus.Eq_0.to.Eq_0.Limit.st.Abs.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-04-18


from . import negative
