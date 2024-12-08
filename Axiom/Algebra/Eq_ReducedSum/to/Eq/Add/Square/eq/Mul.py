from util import *


@apply
def apply(eq_x_bar):
    (x_bar, n), ((x, (S[0], S[n])), S[n]) = eq_x_bar.of(Equal[Indexed, ReducedSum[Sliced] / Symbol])
    return Equal(n * (x_bar[n] - x_bar[n + 1]) ** 2 + (x[n] - x_bar[n + 1]) ** 2, (x[n] - x_bar[n]) * (x[n] - x_bar[n + 1]))


@prove
def prove(Eq):
    from Axiom import Algebra, Discrete

    x = Symbol(real=True, shape=(oo,))
    n, k = Symbol(integer=True)
    x_bar = Symbol(r"\bar {x}", real=True, shape=(oo,))
    Eq << apply(Equal(x_bar[n], ReducedSum(x[:n]) / n))

    Eq << Eq[-1].this.apply(Algebra.Eq.transport, lhs=1)

    Eq << Eq[-1].this.rhs.apply(Algebra.Add.eq.Mul)

    Eq << Eq[-1].this.find(Add ** 2).apply(Algebra.Square.Neg)

    Eq << Algebra.Eq.of.Eq.Div.apply(Eq[-1], Eq[-1].find((~Add) ** 2))

    Eq << Discrete.Eq_ReducedSum.to.Eq.Diff.apply(Eq[0])

    Eq.diff = Eq[-1].this.lhs.doit()

    Eq << Algebra.Eq_ReducedSum.to.Sub.eq.Mul.apply(Eq[0])

    Eq << Eq.diff * n

    Eq << Algebra.Eq.Eq.to.Eq.trans.apply(*Eq[-2:]).reversed




if __name__ == '__main__':
    run()
# created on 2023-11-06
