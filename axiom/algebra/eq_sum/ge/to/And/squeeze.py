from util import *


@apply
def apply(eq, ge):
    (xi, (i, S[0], n)), a = eq.of(Equal[Sum])
    xn, S[a] = ge.of(GreaterEqual)

    assert n > 0
    assert xn == xi._subs(i, n - 1)

    return Equal(xn, a), All[i:n - 1](Equal(xi, 0))


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(real=True, negative=False, shape=(oo,), given=True)
    n = Symbol(integer=True, negative=False, given=True)
    i, j = Symbol(integer=True)
    a = Symbol(real=True, negative=False)
    Eq << apply(Equal(Sum[i:n + 1](x[i]), a), x[n] >= a)

    Eq.eq = Eq[0].this.lhs.apply(Algebra.Sum.eq.Add.split, cond={n})

    Eq << GreaterEqual(Eq.eq.find(Sum), 0, plausible=True)

    Eq << Algebra.Eq.Ge.to.Le.Sub.apply(Eq.eq, Eq[-1])

    Eq << Algebra.Ge.Le.to.Eq.apply(Eq[1], Eq[-1])

    Eq << Eq.eq.subs(Eq[2]).this.apply(Algebra.Eq.simp.terms.common)

    Eq << Eq[-1].this.lhs.limits_subs(i, j)

    Eq << ~Eq[3]

    Eq << Eq[-1].this.expr.apply(Algebra.Ne_0.to.Gt_0)

    Eq << Eq[-3].this.lhs.apply(Algebra.Sum.eq.Add.split, cond={i})

    Eq << Algebra.Cond.Any.to.Any.And.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this().expr.find(Piecewise, Element).simplify()

    Eq << Eq[-1].this.expr.apply(Algebra.Eq.Gt.to.Lt.Sub)


if __name__ == '__main__':
    run()
# created on 2019-04-28
