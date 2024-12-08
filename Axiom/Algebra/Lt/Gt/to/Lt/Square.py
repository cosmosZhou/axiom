from util import *


@apply
def apply(lt, gt):
    x, m = gt.of(Greater)
    S[x], M = lt.of(Less)

    return Less(x * x, Max(m * m, M * M))


@prove
def prove(Eq):
    from Axiom import Algebra

    x, m, M = Symbol(real=True, given=True)
    Eq << apply(x < M, x > m)

    Eq << Eq[-1].apply(Algebra.Cond.of.And.Or, cond=x >= 0)

    Eq << Algebra.And.of.And.apply(Eq[-1])

    Eq << Eq[0].apply(Algebra.Cond.to.And.Or, cond=x >= 0)

    Eq << Algebra.And.to.And.apply(Eq[-1])

    Eq << Algebra.Or.to.Or.invert.apply(Eq[-2])

    Eq << Eq[-1].this.find(And).apply(Algebra.Ge_0.Lt.to.Lt.Square)

    Eq << Eq[-1].this.args[1].apply(Algebra.Lt.to.Lt.relax, Eq[2].rhs)

    Eq << Eq[1].apply(Algebra.Cond.to.And.Or, cond=x > 0)

    Eq << Algebra.And.to.And.apply(Eq[-1])

    Eq << Algebra.Or.to.Or.invert.apply(Eq[-2])

    Eq << Eq[-1].this.find(And).apply(Algebra.Le_0.Gt.to.Lt.Square)

    Eq << Eq[-1].this.find(Less).apply(Algebra.Lt.to.Lt.relax, Eq[2].rhs)

    Eq << Eq[-1].this.find(Greater).apply(Algebra.Gt.to.Ge.relax)





if __name__ == '__main__':
    run()
# created on 2019-08-31
# updated on 2023-05-20
