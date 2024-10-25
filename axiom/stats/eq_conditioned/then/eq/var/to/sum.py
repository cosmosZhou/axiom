from util import *


@apply
def apply(eq_conditioned, n=None):
    ((x, k), S[x[:k].as_boolean()]), S[x[k]] = eq_conditioned.of(Equal[Conditioned[Indexed]])
    if n is None:
        n = k
    return Equal(Variance(ReducedSum(x[:n])), Sum[k:n](Variance(x[k])))


@prove
def prove(Eq):
    from axiom import algebra, stats

    x = Symbol(real=True, shape=(oo,), random=True)
    n = Symbol(integer=True)
    Eq << apply(Equal(x[n] | x[:n], x[n]))

    Eq << Eq[1].lhs.this.find(ReducedSum).apply(algebra.reducedSum.to.sum)

    Eq << Eq[-1].this.rhs.apply(stats.var.sum.to.add.sum)

    Eq.eq_var = Eq[-1].this.find(Sum[2]).apply(algebra.sum.to.add)

    j, i = Eq.eq_var.find(Sum[2]).variables
    Eq << stats.eq_conditioned.then.infer.is_zero.cov.apply(Eq[0], j)

    Eq.infer = Eq[-1].subs(n, i)

    Eq << Eq.eq_var.this.find(Sum[2]).apply(algebra.sum.bool)

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piece)

    Eq << algebra.infer.then.eq.piece.apply(Eq.infer, Eq[-1].find(Piecewise))

    Eq << Eq[-2].subs(Eq[-1])

    t = Symbol(integer=True)
    Eq.infer = Eq.infer.subs(i, t).subs(j, i).subs(t, j)

    Eq << Eq[-1].this.find(Sum[2]).apply(algebra.sum.bool)

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piece)

    Eq << algebra.infer.then.eq.piece.apply(Eq.infer, Eq[-1].find(Piecewise))

    Eq << Eq[-2].subs(Eq[-1])


    Eq << algebra.infer.then.eq.piece.apply(Eq.infer, Eq[-1].find(Piecewise))
    Eq << Eq[-2].subs(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-04-19

# updated on 2023-05-02
