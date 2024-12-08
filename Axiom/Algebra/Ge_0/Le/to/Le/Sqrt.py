from util import *


@apply
def apply(is_nonnegative, le):
    x = is_nonnegative.of(Expr >= 0)
    S[x], y = le.of(Expr <= Expr)

    return LessEqual(sqrt(x), sqrt(y))


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    x, y = Symbol(real=True)
    Eq << apply(x >= 0, LessEqual(x, y))

    Eq << Algebra.Ge_0.to.Ge_0.Sqrt.apply(Eq[0])

    t = Symbol(nonnegative=True)
    Eq << Algebra.Ge.to.Or.split.apply(Eq[-1], t)

    Eq.ou = Eq[-1].subs(t, sqrt(y))

    Eq << Algebra.Le.Ge.to.Ge.trans.apply(Eq[1], Eq[0])

    Eq << Algebra.Ge_0.to.Ge_0.Sqrt.apply(Eq[-1])

    Eq << Sets.Ge.to.In.Interval.apply(Eq[-1])

    Eq << Algebra.Cond.Cond.to.Cond.subs.apply(Eq[-1], Eq.ou, invert=True)

    Eq << Eq[-1].this.find(Greater).apply(Algebra.Gt.to.Gt.Square)

    Eq << Algebra.Cond.Cond.to.Cond.subs.apply(Eq[1], Eq[-1], invert=True)

    Eq << Algebra.And.to.Cond.apply(Eq[-1], 0)




if __name__ == '__main__':
    run()
# created on 2018-07-07
# updated on 2023-05-14
