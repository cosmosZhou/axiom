from util import *


@apply
def apply(greater_than, less_than):
    x, m = greater_than.of(GreaterEqual)
    S[x], M = less_than.of(LessEqual)

    return LessEqual(x * x, Max(m * m, M * M))


@prove
def prove(Eq):
    from axiom import algebra

    x, m, M = Symbol(real=True, given=True)
    Eq << apply(x >= m, x <= M)

    Eq << Eq[-1].apply(algebra.cond.of.et.ou, cond=x >= 0)

    Eq << algebra.et.of.et.apply(Eq[-1])

    Eq << Eq[1].apply(algebra.cond.then.et.ou, cond=x >= 0)

    Eq << algebra.et.then.et.apply(Eq[-1])

    Eq << algebra.ou.then.ou.invert.apply(Eq[-2])

    Eq << Eq[-1].this.find(And).apply(algebra.ge_zero.le.then.le.square)

    Eq << Eq[-1].this.args[1].apply(algebra.le.then.le.relax, Eq[2].rhs)

    Eq << Eq[0].apply(algebra.cond.then.et.ou, cond=x > 0)

    Eq << algebra.et.then.et.apply(Eq[-1])

    Eq << algebra.ou.then.ou.invert.apply(Eq[-2])

    Eq << Eq[-1].this.find(And).apply(algebra.le_zero.ge.then.le.square)

    Eq << Eq[-1].this.args[1].apply(algebra.le.then.le.relax, Eq[2].rhs)

    Eq << Eq[-1].this.args[0].apply(algebra.gt.then.ge.relax)





if __name__ == '__main__':
    run()
# created on 2019-10-25
# updated on 2023-05-13
