from util import *


@apply
def apply(lt_r, γ, λ, k=None, i=None):
    (δ, t), [S[t]] = lt_r.of(Sup[Abs[Indexed]] < Infinity)

    return Equal((1 - λ) * Sum[k:oo](λ ** k * Sum[i: k + 1](γ ** i * δ[t + i])),
                 γ ** Lamda[i](i) @ (λ ** Lamda[i](i) * Identity(oo)) @ δ[t:])



@prove
def prove(Eq):
    from axiom import keras, discrete

    t, k, i = Symbol(integer=True) # time step counter
    δ = Symbol(shape=(oo,), real=True) # TD residual
    λ, γ = Symbol(domain=Interval(0, 1, right_open=True)) # Discount factor: penalty to uncertainty of future rewards; myopic for γ = 0; and far-sighted for γ = 1
    Eq << apply(Less(Sup[t](Abs(δ[t])), oo), γ, λ, k, i)

    Eq << keras.is_finite.imply.eq.matmul.generalized_advantage_estimate.apply(Eq[0], γ, λ, k, i)

    Eq << Eq[-1].this.rhs.find(Pow).apply(discrete.pow.to.matmul, reverse=True)

    


if __name__ == '__main__':
    run()
# created on 2023-10-08
# updated on 2023-10-27
