from util import *


@apply
def apply(eq_x_bar):
    (x_bar, n), ((x, (S[0], S[n])), S[n]) = eq_x_bar.of(Equal[Indexed, ReducedSum[Sliced] / Symbol])
    return Equal(x[n] - x_bar[n + 1], n * (x[n] - x_bar[n]) / (n + 1))


@prove
def prove(Eq):
    from axiom import algebra, discrete

    x = Symbol(real=True, shape=(oo,))
    n, k = Symbol(integer=True)
    x_bar = Symbol(r"\bar {x}", real=True, shape=(oo,))
    Eq << apply(Equal(x_bar[n], ReducedSum(x[:n]) / n))

    Eq << algebra.cond.imply.cond.domain_defined.apply(Eq[0])

    Eq << algebra.et.imply.cond.apply(Eq[-1], 1).reversed + 1

    Eq << algebra.gt.imply.gt.relax.apply(Eq[-1], lower=0)

    Eq << algebra.gt_zero.eq.given.et.mul.apply(Eq[-1], Eq[1], simplify=None)

    Eq << Eq[-1].this.lhs.args[:3:2].apply(algebra.add.to.mul)

    Eq << Eq[-1].this.lhs.args[::2].apply(algebra.add.to.mul)

    Eq << discrete.eq_reducedSum.imply.eq.diff.apply(Eq[0])

    Eq << Eq[-1].this.lhs.doit()

    Eq << Eq[-1] * (n + 1)

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.add, 1)

    Eq << Eq[-1].this.apply(algebra.eq.transport, lhs=1)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1] - (n + 1) * x[n]

    Eq << -Eq[-1]

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(algebra.mul.to.add)
    # Eq << Eq[-1].this.lhs.apply(algebra.add.to.mul)

    

    


if __name__ == '__main__':
    run()
# created on 2023-11-06
