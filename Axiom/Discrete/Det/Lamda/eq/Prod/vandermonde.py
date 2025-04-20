from util import *


@apply
def apply(self, j=None):
    (a, i), (S[i], S[0], n) = self.of(Det[Lamda[Pow]])
    if j is None:
        j = self.generate_var(integer=True, var='j')
    [S[n]] = a.shape
    return Equal(self, Product[j:i, i:n](a[i] - a[j]))


@prove
def prove(Eq):
    from Axiom import Algebra, Discrete, Logic

    n = Symbol(domain=Range(2, oo), given=False)
    a = Symbol(shape=(oo,), complex=True)
    i, j = Symbol(integer=True)
    Eq << apply(Det(Lamda[i:n](a[:n] ** i)), j)

    Eq.initial = Eq[-1].subs(n, 2)

    Eq << Eq.initial.this.rhs.doit(deep=True)

    Eq << Eq[-1].this.lhs.arg.apply(Algebra.Lamda.eq.Matrix).this.lhs.doit()

    Eq.induct = Eq[0].subs(n, n + 1)

    D = Eq.induct.lhs.arg
    def row_transformation(a, *limits):
        n = limits[0][-1]
        (i, *_), (j, *_) = limits
        return Identity(n) - Lamda[j:n, i:n](a[0] * KroneckerDelta(i, j + 1))
    Eq.expand = (row_transformation(a, *D.limits, (j, 0, n + 1)) @ D).this.apply(Discrete.Dot.eq.Lamda)

    Eq << Discrete.Det.eq.Sum.expansion_by_minors.apply(Det(Eq.expand.rhs), i=0)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.Add.shift)

    Eq << Eq[-1].this.rhs.find(Lamda)().expr.simplify()

    Eq << Eq[-1].this.find(Mul[~Sum]).doit()

    Eq.recursion = Eq[-1].this.find(Mul[~Sum]).doit()

    Eq << Eq.recursion.rhs.find(Lamda).this.expr.doit()

    Eq << Eq[-1].this.rhs().expr.simplify()

    Eq << Algebra.All.Eq.of.Eq.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(Algebra.All.Eq.of.Eq)

    Eq << Eq[-1].this.rhs.apply(Algebra.Add.eq.Mul)

    Eq.recursion = Algebra.All.of.All_Eq.Cond.subs.apply(Eq[-1], Eq.recursion)

    Eq << Eq.recursion.rhs.find(Det[~Lamda]).this.find(Sum).doit()

    Eq << Eq[-1].this.rhs.simplify()

    Eq << Eq[-1].this().rhs.find(And).simplify()

    Eq << Eq[-1].this().rhs.find(And).simplify()

    Eq << Eq[-1].this.find(Pow - Mul).apply(Algebra.Add.eq.Mul)

    Eq.recursion = Algebra.All.of.All_Eq.Cond.subs.apply(Eq[-1], Eq.recursion)

    Eq << Eq.recursion.rhs.args[0].this.doit()

    Eq.determinant = Eq[-1].this.find(Product).apply(Algebra.Prod.limits.subs.offset, -1)

    Eq << Algebra.Cond.of.Cond.subs.apply(Eq[0], a[:n], a[1:n + 1])

    k = Eq.determinant.find(Lamda).variable
    Eq << Eq[-1].this.lhs.arg.limits_subs(j, k).this.lhs.arg.limits_subs(i, j).this.rhs.limits_subs(i, i - 1)

    Eq << Eq[-1].this.rhs.apply(Algebra.Prod.limits.subs.offset, -1)

    Eq << Eq.determinant.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul.Prod.eq.Prod)

    Eq << Eq[-1].this.rhs.expr.apply(Algebra.Mul.eq.Prod.limits.unshift)

    Eq << Product[j:i, i:n + 1](Eq[0].rhs.expr).this.apply(Algebra.Prod.eq.Mul.split, cond=slice(0, 1))

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq.recursion = Eq.recursion.subs(Eq[-1])

    D = Eq.recursion.rhs.find(Lamda)
    _i = i.copy(positive=True)
    D = D._subs(i, _i)
    Eq << Discrete.Det.eq.Sum.expansion_by_minors.apply(Det(D), j=0)

    Eq << Algebra.All.of.Cond.apply(Eq[-1], _i)

    Eq << Algebra.All.of.All_Eq.Cond.subs.apply(Eq[-1], Eq.recursion)

    Eq << Eq.expand.apply(Discrete.EqDet.of.Eq)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[-1].this.lhs.apply(Discrete.Det.eq.Mul)

    Eq << Eq[-1].this.lhs.args[0].doit()

    Eq << Imply(Eq[0], Eq.induct, plausible=True)

    Eq << Logic.Cond.of.Cond.Imp.induct.apply(Eq.initial, Eq[-1], n=n, start=2)





if __name__ == '__main__':
    run()

# created on 2020-08-21
# updated on 2023-05-21

