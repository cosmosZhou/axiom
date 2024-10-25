from util import *


@apply
def apply(eq_sum, all_is_nonnegative):
    (xi, (i, S[0], n)), a = eq_sum.of(Equal[Sum])
    S[xi], (S[i], S[0], S[n]) = all_is_nonnegative.of(All[Expr >= 0])

    return All[i:n](xi <= a)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True, shape=(oo,), given=True)
    n = Symbol(integer=True, given=True, negative=False)
    i, j = Symbol(integer=True)
    a = Symbol(real=True, given=True)
    Eq << apply(Equal(Sum[i:n](x[i]), a), All[i:n](x[i] >= 0))

    Eq << ~Eq[2]

    Eq << Eq[0].this.lhs.limits_subs(i, j)

    Eq << Eq[0].this.lhs.apply(algebra.sum.to.add.split, cond={i})

    Eq << algebra.cond.any.then.any.et.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this().expr.find(Piecewise, Element).simplify()

    Eq.any_is_negative = Eq[-1].this.expr.apply(algebra.eq.gt.then.lt.sub)

    Eq << algebra.all.then.all.limits.restrict.apply(Eq[1], Range(n) - {i})

    Eq << Eq[-1].limits_subs(i, j)

    Eq << algebra.all_ge_zero.then.ge_zero.sum.apply(Eq[-1])

    Eq << algebra.cond.any.then.any.et.apply(Eq[-1], Eq.any_is_negative)




if __name__ == '__main__':
    run()
# created on 2023-08-20
