from util import *


@apply
def apply(lt, gt):
    x, m = gt.of(Greater)
    S[x], M = lt.of(Less)

    return Less(x * x, Max(m * m, M * M))


@prove
def prove(Eq):
    from axiom import algebra

    x, m, M = Symbol(real=True, given=True)
    Eq << apply(x < M, x > m)

    Eq << Eq[-1].apply(algebra.cond.of.et.ou, cond=x >= 0)

    Eq << algebra.et.of.et.apply(Eq[-1])

    Eq << Eq[0].apply(algebra.cond.then.et.ou, cond=x >= 0)

    Eq << algebra.et.then.et.apply(Eq[-1])

    Eq << algebra.ou.then.ou.invert.apply(Eq[-2])

    Eq << Eq[-1].this.find(And).apply(algebra.ge_zero.lt.then.lt.square)

    Eq << Eq[-1].this.args[1].apply(algebra.lt.then.lt.relax, Eq[2].rhs)

    Eq << Eq[1].apply(algebra.cond.then.et.ou, cond=x > 0)

    Eq << algebra.et.then.et.apply(Eq[-1])

    Eq << algebra.ou.then.ou.invert.apply(Eq[-2])

    Eq << Eq[-1].this.find(And).apply(algebra.le_zero.gt.then.lt.square)

    Eq << Eq[-1].this.find(Less).apply(algebra.lt.then.lt.relax, Eq[2].rhs)

    Eq << Eq[-1].this.find(Greater).apply(algebra.gt.then.ge.relax)





if __name__ == '__main__':
    run()
# created on 2019-08-31
# updated on 2023-05-20
