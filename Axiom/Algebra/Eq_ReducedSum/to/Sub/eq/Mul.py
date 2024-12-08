from util import *


@apply
def apply(eq_x_bar):
    (x_bar, n), ((x, (S[0], S[n])), S[n]) = eq_x_bar.of(Equal[Indexed, ReducedSum[Sliced] / Symbol])
    return Equal(x[n] - x_bar[n + 1], n * (x[n] - x_bar[n]) / (n + 1))


@prove
def prove(Eq):
    from Axiom import Algebra, Discrete

    x = Symbol(real=True, shape=(oo,))
    n, k = Symbol(integer=True)
    x_bar = Symbol(r"\bar {x}", real=True, shape=(oo,))
    Eq << apply(Equal(x_bar[n], ReducedSum(x[:n]) / n))

    Eq << Algebra.Cond.to.Cond.domain_defined.apply(Eq[0])

    Eq << Algebra.And.to.Cond.apply(Eq[-1], 1).reversed + 1

    Eq << Algebra.Gt.to.Gt.relax.apply(Eq[-1], lower=0)

    Eq << Algebra.Gt_0.Eq.of.And.Mul.apply(Eq[-1], Eq[1], simplify=None)

    Eq << Eq[-1].this.lhs.args[:3:2].apply(Algebra.Add.eq.Mul)

    Eq << Eq[-1].this.lhs.args[::2].apply(Algebra.Add.eq.Mul)

    Eq << Discrete.Eq_ReducedSum.to.Eq.Diff.apply(Eq[0])

    Eq << Eq[-1].this.lhs.doit()

    Eq << Eq[-1] * (n + 1)

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul.eq.Add, 1)

    Eq << Eq[-1].this.apply(Algebra.Eq.transport, lhs=1)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1] - (n + 1) * x[n]

    Eq << -Eq[-1]

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(Algebra.Mul.eq.Add)
    # Eq << Eq[-1].this.lhs.apply(Algebra.Add.eq.Mul)






if __name__ == '__main__':
    run()
# created on 2023-11-06
