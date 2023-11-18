from util import *


@apply
def apply(lt_r, γ, λ, k=None, i=None):
    (δ, t), [S[t]] = lt_r.of(Sup[Abs[Indexed]] < Infinity)

    return Equal((1 - λ) * Sum[k:oo](λ ** k * Sum[i: k + 1](γ ** i * δ[t + i])),
                 (γ * λ) ** Lamda[i](i) @ δ[t:])    


@prove
def prove(Eq):
    from axiom import algebra, calculus, sets, discrete

    t, k, i = Symbol(integer=True) # time step counter
    δ = Symbol(shape=(oo,), real=True) # TD residual
    λ, γ = Symbol(domain=Interval(0, 1, right_open=True)) # Discount factor: penalty to uncertainty of future rewards; myopic for γ = 0; and far-sighted for γ = 1
    Eq << apply(Less(Sup[t](Abs(δ[t])), oo), γ, λ, k, i)

    n = Symbol(integer=True)
    Eq << Eq[1].lhs._subs(oo, n).this.find(Sum[~Mul[Sum]]).apply(algebra.mul.to.sum)

    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.limits.swap.intlimit)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.limits.separate)

    i = Eq[-1].rhs.variable
    Eq << Eq[-1].this.rhs.find(Mul[~Sum]).apply(algebra.sum.limits.subs.offset, i)

    Eq << Eq[-1].this.find(Pow[Add]).apply(algebra.pow.to.mul.split.exponent)

    Eq << Unequal(λ, 1, plausible=True)

    Eq << algebra.ne.imply.eq.sum.geometric_series.apply(Eq[-1], Eq[-2].rhs.find(Mul[~Sum]))

    Eq << Eq[-3].subs(Eq[-1]) * (1 - λ)

    Eq << Eq[-1].this.find(Pow * Pow).apply(algebra.mul.to.add, 3)

    Eq << Eq[-1].this.rhs.find(Pow * Pow * Pow).args[1:3].apply(algebra.mul.to.pow.add.exponent)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.to.add)

    Eq << Eq[-1].this.find(Pow * Pow).args[:2].apply(algebra.mul.to.pow.mul.base)

    Eq << calculus.eq.imply.eq.limit.apply(Eq[-1], (n, oo))

    Eq << Eq[-1].this.lhs.apply(calculus.limit.to.mul)

    Eq << Eq[-1].this.lhs.find(Limit).apply(calculus.limit.to.sum)

    Eq << Eq[-1].this.find(Limit).apply(calculus.limit.to.add)

    Eq << Eq[-1].this.find(Limit).apply(calculus.limit.to.mul)

    Eq.limit = Eq[-1].this.find(Limit).apply(calculus.limit.to.sum)

    i = Eq.limit.rhs.find(Sum).variable
    Eq.lt = Less(Abs(γ, evaluate=False), 1, plausible=True)

    Eq << Eq.lt.this.lhs.doit()

    Eq << Eq[0].this.lhs.limits_subs(t, i).this.lhs.apply(algebra.sup.limits.subs.offset, t)

    Eq << sets.abs_lt.is_finite.imply.is_real.sum.apply(Eq.lt, Eq[-1], simplify=None)

    Eq << Eq[-1].this.lhs.apply(calculus.sum.to.limit, n)

    Eq.lt = Less(Abs(λ, evaluate=False), 1, plausible=True)

    Eq << Eq.lt.this.lhs.doit()

    Eq << calculus.abs_lt.imply.is_zero.limit.geometric_series.apply(Eq.lt, n)

    Eq << calculus.is_zero.is_limited.imply.is_zero.limit.algebraic_limit_theorem.apply(Eq[-1], Eq[-2])

    Eq << Eq.limit.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(discrete.sum.to.matmul)

    Eq << Eq[-1].this.rhs.T

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.to.pow)

    

    # https://arxiv.org/pdf/1506.02438.pdf Eq(16)
    
    


if __name__ == '__main__':
    run()
# created on 2023-04-08
# updated on 2023-10-08
