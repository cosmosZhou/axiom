from util import *


@apply
def apply(self):
    (sgm, sgm_t), n = self.of((Expr - Expr) / Expr)
    n += 1
    (xi, xj), (j, S[0], i), (S[i], S[0], S[n]) = sgm.of(Sum[(Expr - Expr) ** 2])
    (_xi, xt), (_i, S[0], S[n]) = sgm_t.of(Sum[(Expr - Expr) ** 2])
    x, t = xt.of(Indexed)

    assert _xi == x[_i]
    if xi._has(j):
        xi, xi = xj, xi

    assert xi == x[i]
    assert xj == x[j]

    assert 0 <= t < n

    return Equal(self, Sum[i:n]((x[i] - (Sum[i:n](x[i]) - xt) / (n - 1)) ** 2) - (xt - (Sum[i:n](x[i]) - xt) / (n - 1)) ** 2)


@prove
def prove(Eq):
    from Axiom import Algebra

    i, j = Symbol(integer=True)
    n = Symbol(domain=Range(2, oo))
    x = Symbol(integer=True, shape=(oo,))
    t = Symbol(domain=Range(n))
    Eq << apply((Sum[j:i, i:n]((x[i] - x[j]) ** 2) - Sum[i:n]((x[i] - x[t]) ** 2)) / (n - 1))

    y = Symbol(Lamda[i:n - 1](Piecewise((x[i], i < t),(x[i + 1], True))))
    Eq << y[i].this.definition

    Eq.y_sum = Algebra.Eq_Piece.to.Eq.Sum.apply(Eq[1], Sum[i:n-1](y[i]))

    Eq << Algebra.Sum.Square.eq.Div.Sum.Square.apply(Sum[i:n-1]((y[i] - Sum[i:n - 1](y[i]) / (n - 1)) ** 2))

    Eq << Eq[-1].subs(Eq.y_sum).reversed

    Eq << Algebra.Eq_Piece.to.Eq.Sum.apply(Eq[1], Eq[-1].rhs)

    Eq << Algebra.Eq.Eq.to.Eq.trans.apply(Eq[-2], Eq[-1])

    Eq << Algebra.Sum.Square.eq.Add.st.double_limits.apply(Eq[-1].lhs.args[1])

    Eq << Eq[-1].subs(Eq.y_sum)

    Eq << Algebra.Eq_Piece.to.Eq.Sum.apply(Eq[1], Sum[i:n - 1](y[i] ** 2))

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.rhs.find(Mul).apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.rhs.find(Mul).apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.rhs.find(Add ** 2).apply(Algebra.Square.eq.Add)

    Eq << Eq[0].lhs.find(Sum).this.apply(Algebra.Sum.Square.eq.Add.st.double_limits)

    Eq << Eq[-2] - Eq[-1]

    Eq << Eq[0].lhs.find(-~Sum).this.expr.apply(Algebra.Square.eq.Add)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.Add)

    Eq << Eq[-3] + Eq[-1]

    Eq << Eq[-1].this.apply(Algebra.Eq.transport, lhs=slice(0, None, 2))

    Eq << Eq[0].subs(Eq[-1].reversed)





if __name__ == '__main__':
    run()
# created on 2019-11-27
# updated on 2023-05-20