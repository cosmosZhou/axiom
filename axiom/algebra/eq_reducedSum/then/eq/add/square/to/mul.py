from util import *


@apply
def apply(eq_x_bar):
    (x_bar, n), ((x, (S[0], S[n])), S[n]) = eq_x_bar.of(Equal[Indexed, ReducedSum[Sliced] / Symbol])
    return Equal(n * (x_bar[n] - x_bar[n + 1]) ** 2 + (x[n] - x_bar[n + 1]) ** 2, (x[n] - x_bar[n]) * (x[n] - x_bar[n + 1]))


@prove
def prove(Eq):
    from axiom import algebra, discrete

    x = Symbol(real=True, shape=(oo,))
    n, k = Symbol(integer=True)
    x_bar = Symbol(r"\bar {x}", real=True, shape=(oo,))
    Eq << apply(Equal(x_bar[n], ReducedSum(x[:n]) / n))

    Eq << Eq[-1].this.apply(algebra.eq.transport, lhs=1)

    Eq << Eq[-1].this.rhs.apply(algebra.add.to.mul)

    Eq << Eq[-1].this.find(Add ** 2).apply(algebra.square.negate)

    Eq << algebra.eq.of.eq.div.apply(Eq[-1], Eq[-1].find((~Add) ** 2))

    Eq << discrete.eq_reducedSum.then.eq.diff.apply(Eq[0])

    Eq.diff = Eq[-1].this.lhs.doit()

    Eq << algebra.eq_reducedSum.then.eq.sub.to.mul.apply(Eq[0])

    Eq << Eq.diff * n

    Eq << algebra.eq.eq.then.eq.trans.apply(*Eq[-2:]).reversed




if __name__ == '__main__':
    run()
# created on 2023-11-06
