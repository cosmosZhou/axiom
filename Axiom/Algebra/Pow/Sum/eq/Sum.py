from util import *


@apply
def apply(self, var='k'):
    (xi, (i, S[0], n)), m = self.of(Pow[Sum])
    k = self.generate_var(integer=True, shape=(oo,), var=var)
    return Equal(self, Sum[k[:n]:Equal(ReducedSum(k[:n]), m):CartesianSpace(Range(0, m + 1), n)](
        Factorial(m) / Product[i:n](Factorial(k[i])) * Product[i:n](xi ** k[i])))


@prove
def prove(Eq):
    from Axiom import Algebra, Discrete, Sets

    n = Symbol(integer=True, positive=True, given=False)
    x = Symbol(complex=True, shape=(oo,))
    i = Symbol(integer=True)
    m = Symbol(integer=True, nonnegative=True)
    Eq << apply(Sum[i:n](x[i]) ** m)

    Eq << Eq[0].subs(n, 1)

    Eq << Eq[1].this.rhs.apply(Algebra.Sum.Bool)

    Eq << Eq[-1].this.find(Bool).apply(Algebra.Bool.eq.Delta)

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.base.apply(Algebra.Sum.eq.Add.pop)

    Eq << Eq[-1].this.lhs.apply(Discrete.Pow.eq.Sum.Binom.Newton)

    Eq << Eq[-1].this.find(Binomial).apply(Discrete.Binom.eq.Mul)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.Mul)

    Eq << Eq[-1].this.find(Product).apply(Algebra.Prod.eq.Mul.pop)

    Eq << Eq[-1].this.find((~Product) ** -1).apply(Algebra.Prod.eq.Mul.pop)

    Eq << Eq[-1].this.rhs.find(Equal[~ReducedSum]).apply(Algebra.ReducedSum.eq.Add.pop)

    Eq << Eq[-1].this.rhs.find(Equal).apply(Algebra.Eq.transport, lhs=0)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.pop.CartesianSpace.Cond)

    k = Eq[-1].lhs.variable
    Eq << Eq[-1].this.rhs.limits_subs(Eq[-1].rhs.variables[1], k)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.separate)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Algebra.Sum.eq.Mul)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Algebra.Sum.Bool)

    Eq << Eq[-1].this.rhs().find(And).apply(Sets.Eq_Sum.In_CartesianSpace.equ.And)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Algebra.Sum.limits.absorb)

    Eq << Eq[0].subs(m, m - k)

    Eq << Algebra.Or.to.Imply.apply(Eq[-1], 1)

    Eq << Eq[-1].this.lhs.apply(Sets.In_Range.of.In.Range.restrict, upper=m + 1)

    Eq << Eq[-1].this.lhs.apply(Sets.In.Neg)

    Eq << Eq[-1].this.lhs.apply(Sets.In.Add, m)

    Eq << Algebra.Imply.to.All.single_variable.apply(Eq[-1])

    Eq << Eq[-1].this.expr * (x[n] ** k / (Factorial(m - k) * Factorial(k)))

    Eq << Eq[-1].this.expr.rhs.find(Sum).apply(Algebra.Sum.eq.Mul, simplify=1)

    Eq << Algebra.All_Eq.to.Eq.Sum.apply(Eq[-1])

    Eq << Imply(Eq[0], Eq.induct, plausible=True)

    Eq << Algebra.Eq.Imply.to.Eq.induct.apply(Eq[1], Eq[-1], n, 1)


if __name__ == '__main__':
    run()
# created on 2023-08-20

