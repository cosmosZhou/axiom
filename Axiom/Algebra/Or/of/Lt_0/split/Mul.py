from util import *


@apply
def apply(given):
    x, y = given.of(Mul < 0)
    return Or(And(x > 0, y < 0), And(x < 0, y > 0))


@prove
def prove(Eq):
    from Axiom import Algebra, Logic

    x, y = Symbol(real=True, given=True)
    Eq << apply(x * y < 0)

    Eq << ~Eq[-1]

    Eq << Eq[-1].this.args[0].apply(Logic.Or_AndNot.of.Or, pivot=1)

    Eq << Eq[-1].this.find(Or).apply(Logic.Or_AndNot.of.Or, pivot=0)

    Eq << Logic.OrAndS.of.And_Or.apply(Eq[-1], 1, simplify=None)

    Eq << Eq[-1].this.find(And).apply(Logic.OrAndS.of.And_Or, 1)

    Eq << Eq[-1].this.find((Expr > 0) & (Expr >= 0)).apply(Algebra.Ge_0.of.Ge_0.Gt_0)

    Eq << Eq[-1].this.find((Expr > 0) & (Expr >= 0)).apply(Algebra.Ge_0.of.Ge_0.Gt_0)

    Eq << Eq[-1].this.find(And).args[:2].apply(Algebra.Ge_0.of.Le_0.Lt_0)

    Eq << Algebra.Cond.of.Cond.Cond.subs.apply(Eq[0], Eq[-1], invert=True)

    Eq << Eq[0].subs(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2023-04-15
# updated on 2023-05-13
