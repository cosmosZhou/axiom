from util import *


@apply
def apply(eq_x_bar):
    (x_bar, n), ((x, (S[0], S[n])), S[n]) = eq_x_bar.of(Equal[Indexed, ReducedSum[Sliced] / Symbol])
    return Equal(Difference[n](x_bar[n]), (x[n] - x_bar[n]) / (n + 1))


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True, shape=(oo,))
    n, k = Symbol(integer=True)
    x_bar = Symbol(r"\bar {x}", real=True, shape=(oo,))
    Eq << apply(Equal(x_bar[n], ReducedSum(x[:n]) / n))

    Eq << Eq[-1].this.lhs.doit()

    Eq << Eq[0].subs(n, n + 1) - Eq[0]

    Eq << Eq[-1].this.find(ReducedSum).apply(algebra.reducedSum.to.add.pop)

    Eq << Eq[0] * n

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.rhs.apply(algebra.add.to.mul.together)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(algebra.mul.to.add)

    


if __name__ == '__main__':
    run()
# created on 2023-11-06
