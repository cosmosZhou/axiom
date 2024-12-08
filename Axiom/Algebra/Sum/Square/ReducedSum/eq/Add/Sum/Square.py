from util import *


@apply
def apply(self, j=None):
    expr, limit = self.of(Sum)
    x_sub_x_means = expr.of(Expr ** 2)

    try:
        i, S[0], n = limit
    except:
        i, = limit
        domain = expr.domain_defined(i)
        S[0], n = domain.of(Range)

    assert i.is_integer

    xi, x_means = x_sub_x_means.of(Expr - Expr)

    x, S[i] = xi.of(Indexed)

    x_sum = x_means * n

    S[x[:n]] = x_sum.of(ReducedSum)
    if j is None:
        j = expr.generate_var(integer=True, excludes={i}, var='j')
    return Equal(self, ReducedSum(x[:n] ** 2) - x_sum ** 2 / n)


@prove
def prove(Eq):
    from Axiom import Algebra

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    x = Symbol(integer=True, shape=(oo,))
    Eq << apply(Sum[i:n]((x[i] - ReducedSum(x[:n]) / n) ** 2))

    Eq << Eq[0].this.lhs.apply(Algebra.Sum.Square.ReducedSum.eq.Div.Sum.Square)

    Eq << Eq[-1] * n

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.Square.eq.Add.st.double_limits)

    Eq << Eq[-1].this.find(ReducedSum).apply(Algebra.ReducedSum.eq.Sum)

    Eq << Eq[-1].this.find(ReducedSum).apply(Algebra.ReducedSum.eq.Sum)


if __name__ == '__main__':
    run()
# created on 2023-10-08
