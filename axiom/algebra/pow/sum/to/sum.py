from util import *


@apply
def apply(self, var='k'):
    (xi, (i, S[0], n)), m = self.of(Pow[Sum])
    k = self.generate_var(integer=True, shape=(oo,), var=var)
    return Equal(self, Sum[k[:n]:Equal(ReducedSum(k[:n]), m):CartesianSpace(Range(0, m + 1), n)](
        Factorial(m) / Product[i:n](Factorial(k[i])) * Product[i:n](xi ** k[i])))


@prove
def prove(Eq):
    from axiom import algebra, discrete, sets

    n = Symbol(integer=True, positive=True, given=False)
    x = Symbol(complex=True, shape=(oo,))
    i = Symbol(integer=True)
    m = Symbol(integer=True, nonnegative=True)
    Eq << apply(Sum[i:n](x[i]) ** m)

    Eq << Eq[0].subs(n, 1)

    Eq << Eq[1].this.rhs.apply(algebra.sum.bool)

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.delta)

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.base.apply(algebra.sum.to.add.pop)

    Eq << Eq[-1].this.lhs.apply(discrete.pow.to.sum.binom.Newton)

    Eq << Eq[-1].this.find(Binomial).apply(discrete.binom.to.mul)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.mul)

    Eq << Eq[-1].this.find(Product).apply(algebra.prod.to.mul.pop)

    Eq << Eq[-1].this.find((~Product) ** -1).apply(algebra.prod.to.mul.pop)

    Eq << Eq[-1].this.rhs.find(Equal[~ReducedSum]).apply(algebra.reducedSum.to.add.pop)

    Eq << Eq[-1].this.rhs.find(Equal).apply(algebra.eq.transport, lhs=0)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.limits.pop.cartesianSpace.cond)

    k = Eq[-1].lhs.variable
    Eq << Eq[-1].this.rhs.limits_subs(Eq[-1].rhs.variables[1], k)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.limits.separate)

    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.to.mul)

    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.bool)

    Eq << Eq[-1].this.rhs().find(And).apply(sets.eq_sum.el_cartesianSpace.to.et)

    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.limits.absorb)

    Eq << Eq[0].subs(m, m - k)

    Eq << algebra.ou.then.infer.apply(Eq[-1], 1)

    Eq << Eq[-1].this.lhs.apply(sets.el_range.of.el.range.restrict, upper=m + 1)

    Eq << Eq[-1].this.lhs.apply(sets.el.negate)

    Eq << Eq[-1].this.lhs.apply(sets.el.add, m)

    Eq << algebra.infer.then.all.single_variable.apply(Eq[-1])

    Eq << Eq[-1].this.expr * (x[n] ** k / (Factorial(m - k) * Factorial(k)))

    Eq << Eq[-1].this.expr.rhs.find(Sum).apply(algebra.sum.to.mul, simplify=1)

    Eq << algebra.all_eq.then.eq.sum.apply(Eq[-1])

    Eq << Infer(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.eq.infer.then.eq.induct.apply(Eq[1], Eq[-1], n, 1)


if __name__ == '__main__':
    run()
# created on 2023-08-20

