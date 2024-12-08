from util import *


@apply
def apply(greater_than, less_than):
    x, m = greater_than.of(GreaterEqual)
    S[x], M = less_than.of(LessEqual)

    return LessEqual(x * x, Max(m * m, M * M))


@prove
def prove(Eq):
    from Axiom import Algebra

    x, m, M = Symbol(real=True, given=True)
    Eq << apply(x >= m, x <= M)

    Eq << Eq[-1].apply(Algebra.Cond.of.And.Or, cond=x >= 0)

    Eq << Algebra.And.of.And.apply(Eq[-1])

    Eq << Eq[1].apply(Algebra.Cond.to.And.Or, cond=x >= 0)

    Eq << Algebra.And.to.And.apply(Eq[-1])

    Eq << Algebra.Or.to.Or.invert.apply(Eq[-2])

    Eq << Eq[-1].this.find(And).apply(Algebra.Ge_0.Le.to.Le.Square)

    Eq << Eq[-1].this.args[1].apply(Algebra.Le.to.Le.relax, Eq[2].rhs)

    Eq << Eq[0].apply(Algebra.Cond.to.And.Or, cond=x > 0)

    Eq << Algebra.And.to.And.apply(Eq[-1])

    Eq << Algebra.Or.to.Or.invert.apply(Eq[-2])

    Eq << Eq[-1].this.find(And).apply(Algebra.Le_0.Ge.to.Le.Square)

    Eq << Eq[-1].this.args[1].apply(Algebra.Le.to.Le.relax, Eq[2].rhs)

    Eq << Eq[-1].this.args[0].apply(Algebra.Gt.to.Ge.relax)





if __name__ == '__main__':
    run()
# created on 2019-10-25
# updated on 2023-05-13
