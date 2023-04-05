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
    from axiom import algebra, discrete

    n = Symbol(domain=Range(2, oo), given=False)
    a = Symbol(shape=(oo,), complex=True)
    i, j = Symbol(integer=True)
    Eq << apply(Det(Lamda[i:n](a[:n] ** i)), j)

    Eq.initial = Eq[-1].subs(n, 2)

    Eq << Eq.initial.this.rhs.doit(deep=True)

    Eq << Eq[-1].this.lhs.arg.apply(algebra.lamda.to.matrix).this.lhs.doit()

    Eq.induct = Eq[0].subs(n, n + 1)

    D = Eq.induct.lhs.arg
    def row_transformation(a, *limits):
        n = limits[0][-1]
        (i, *_), (j, *_) = limits
        return Identity(n) - Lamda[j:n, i:n](a[0] * KroneckerDelta(i, j + 1))
    Eq.expand = (row_transformation(a, *D.limits, (j, 0, n + 1)) @ D).this.apply(discrete.matmul.to.lamda)

    Eq << discrete.det.to.sum.expansion_by_minors.apply(Det(Eq.expand.rhs), i=0)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add.shift)

    Eq << Eq[-1].this.rhs.args[0].args[0].arg().expr.simplify()

    Eq << Eq[-1].this.rhs.args[0].args[1].doit()

    Eq.recursion = Eq[-1].this.rhs.args[1].expr.args[-1].doit()

    Eq << Eq.recursion.rhs.args[0].arg.this.expr.doit()

    Eq << Eq[-1].this.rhs().expr.simplify()

    Eq << algebra.eq.imply.all_eq.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(algebra.eq.imply.all_eq)

    Eq << Eq[-1].this.expr.rhs.expand().this.expr.rhs.collect(Eq[-1].rhs.args[1].args[-1])

    Eq.recursion = algebra.all_eq.cond.imply.all.subs.apply(Eq[-1], Eq.recursion)

    Eq << Eq.recursion.rhs.args[1].expr.args[1].arg.this.expr.args[0].expr.doit()

    Eq << Eq[-1].this.rhs.simplify(deep=True, wrt=Eq[-1].rhs.variable)

    Eq << Eq[-1].this.expr.rhs.args[0].expr.expand().this.expr.rhs.args[0].expr.collect(Eq[-1].rhs.args[0][0].args[1].args[-1])

    Eq.recursion = algebra.all_eq.cond.imply.all.subs.apply(Eq[-1], Eq.recursion)

    Eq << Eq.recursion.rhs.args[0].this.doit()

    Eq.determinant = Eq[-1].this.find(Product).apply(algebra.prod.limits.subs.offset, -1)

    Eq << algebra.eq.imply.eq.subs.apply(Eq[0], a[:n], a[1:n + 1])

    k = Eq.determinant.find(Lamda).variable
    Eq << Eq[-1].this.lhs.arg.limits_subs(j, k).this.lhs.arg.limits_subs(i, j).this.rhs.limits_subs(i, i - 1)

    Eq << Eq[-1].this.rhs.apply(algebra.prod.limits.subs.offset, -1)

    Eq << Eq.determinant.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.prod)

    Eq << Eq[-1].this.rhs.expr.apply(algebra.mul.to.prod.limits.unshift)

    Eq << Product[j:i, i:n + 1](Eq[0].rhs.expr).this.apply(algebra.prod.to.mul.split, cond=slice(0, 1))

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq.recursion = Eq.recursion.subs(Eq[-1])

    D = Eq.recursion.rhs.args[1].expr.args[1].arg
    _i = i.copy(positive=True)
    D = D._subs(i, _i)
    Eq << discrete.det.to.sum.expansion_by_minors.apply(Det(D), j=0)

    Eq << algebra.cond.imply.all.apply(Eq[-1], _i)

    Eq << algebra.all_eq.cond.imply.all.subs.apply(Eq[-1], Eq.recursion)

    Eq << Eq.expand.apply(discrete.eq.imply.eq.det)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[-1].this.lhs.apply(discrete.det.to.mul)

    Eq << Eq[-1].this.lhs.args[0].doit()


    Eq << Infer(Eq[0], Eq.induct, plausible=True)
    Eq << algebra.cond.infer.imply.cond.induct.apply(Eq.initial, Eq[-1], n=n, start=2)




if __name__ == '__main__':
    run()

# created on 2020-08-21
# updated on 2023-03-18

from . import st
