from util import *


@apply
def apply(eq):
    (A, t), ((γ, (i, (S[i],))), (δ, (S[t], S[oo]))) = eq.of(Equal[Indexed, Symbol ** Lamda @ Sliced])

    return Equal(A[t], δ[t] + γ * A[t + 1])


@prove
def prove(Eq):
    from axiom import discrete, algebra

    t, i = Symbol(integer=True) # time step counter
    A, δ = Symbol(shape=(oo,), real=True) # advantages and TD residuals
    γ = Symbol(domain=Interval(0, 1, right_open=True)) # Discount factor
    Eq << apply(Equal(A[t], γ ** Lamda[i](i) @ δ[t:]))

    Eq << Eq[0].this.rhs.apply(discrete.matmul.to.add.shift)

    Eq << Eq[-1].this.find(Pow).apply(algebra.pow.to.mul.split.exponent)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.to.pow)

    Eq << Eq[0].subs(t, t + 1)

    Eq << Eq[-2].subs(Eq[-1].reversed)


if __name__ == '__main__':
    run()
# created on 2023-11-02
