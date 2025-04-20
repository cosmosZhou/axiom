from util import *


@apply
def apply(is_nonnegative, le):
    x = is_nonnegative.of(Expr >= 0)
    S[x], y = le.of(Expr <= Expr)

    return LessEqual(sqrt(x), sqrt(y))


@prove
def prove(Eq):
    from Axiom import Algebra, Set, Logic

    x, y = Symbol(real=True)
    Eq << apply(x >= 0, LessEqual(x, y))

    Eq << Algebra.Ge_0.Sqrt.of.Ge_0.apply(Eq[0])

    t = Symbol(nonnegative=True)
    Eq << Algebra.Or.of.Ge.split.apply(Eq[-1], t)

    Eq.ou = Eq[-1].subs(t, sqrt(y))

    Eq << Algebra.Ge.of.Le.Ge.apply(Eq[1], Eq[0])

    Eq << Algebra.Ge_0.Sqrt.of.Ge_0.apply(Eq[-1])

    Eq << Set.Mem.Icc.of.Ge.apply(Eq[-1])

    Eq << Algebra.Cond.of.Cond.Cond.subs.apply(Eq[-1], Eq.ou, invert=True)

    Eq << Eq[-1].this.find(Greater).apply(Algebra.GtSquare.of.Gt)

    Eq << Algebra.Cond.of.Cond.Cond.subs.apply(Eq[1], Eq[-1], invert=True)

    Eq << Logic.Cond.of.And.apply(Eq[-1], 0)




if __name__ == '__main__':
    run()
# created on 2018-07-07
# updated on 2023-05-14
