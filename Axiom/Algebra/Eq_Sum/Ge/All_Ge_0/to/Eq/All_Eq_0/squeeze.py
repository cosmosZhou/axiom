from util import *


@apply
def apply(eq_sum, ge, all_is_nonnegative):
    (xi, (i, S[0], n)), a = eq_sum.of(Equal[Sum])
    xn, S[a] = ge.of(GreaterEqual)

    assert n > 0
    assert xn == xi._subs(i, n - 1)
    S[xi], (S[i], S[0], S[n]) = all_is_nonnegative.of(All[Expr >= 0])

    return Equal(xn, a), All[i:n - 1](Equal(xi, 0))


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(real=True, shape=(oo,), given=True)
    n = Symbol(integer=True, given=True, negative=False)
    i, j = Symbol(integer=True)
    a = Symbol(real=True)
    Eq << apply(Equal(Sum[i:n + 1](x[i]), a), x[n] >= a, All[i:n + 1](x[i] >= 0))

    Eq.eq = Eq[0].this.lhs.apply(Algebra.Sum.eq.Add.pop)

    Eq.All_is_nonnegative = Algebra.All.to.All.limits.restrict.apply(Eq[2], domain=Range(n))

    Eq << Algebra.All_Ge_0.to.Ge_0.Sum.apply(Eq.All_is_nonnegative)

    Eq << Algebra.Eq.Ge.to.Le.Sub.apply(Eq.eq, Eq[-1])

    Eq << Algebra.Ge.Le.to.Eq.apply(Eq[1], Eq[-1])

    Eq << Eq.eq.subs(Eq[3])

    Eq << Eq[-1].this.apply(Algebra.Eq.simp.terms.common)

    Eq << Eq[-1].this.lhs.limits_subs(i, j)

    Eq << ~Eq[4]

    Eq << Algebra.All.Any.to.Any.And.apply(Eq.All_is_nonnegative, Eq[-1])

    Eq << Eq[-3].this.lhs.apply(Algebra.Sum.eq.Add.split, cond={i})

    Eq << Algebra.Cond.Any.to.Any.And.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this().expr.find(Piecewise, Element).simplify()

    Eq.any_is_negative = Eq[-1].this.expr.apply(Algebra.Eq.Gt.to.Lt.Sub)

    Eq << Algebra.All.to.All.limits.restrict.apply(Eq.All_is_nonnegative, Range(n) - {i})

    Eq << Eq[-1].limits_subs(i, j)

    Eq << Algebra.All_Ge_0.to.Ge_0.Sum.apply(Eq[-1])

    Eq << Algebra.Cond.Any.to.Any.And.apply(Eq[-1], Eq.any_is_negative)


if __name__ == '__main__':
    run()
# created on 2019-04-27
