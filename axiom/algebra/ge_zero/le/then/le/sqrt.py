from util import *


@apply
def apply(is_nonnegative, le):
    x = is_nonnegative.of(Expr >= 0)
    S[x], y = le.of(Expr <= Expr)

    return LessEqual(sqrt(x), sqrt(y))


@prove
def prove(Eq):
    from axiom import algebra, sets

    x, y = Symbol(real=True)
    Eq << apply(x >= 0, LessEqual(x, y))

    Eq << algebra.ge_zero.then.ge_zero.sqrt.apply(Eq[0])

    t = Symbol(nonnegative=True)
    Eq << algebra.ge.then.ou.split.apply(Eq[-1], t)

    Eq.ou = Eq[-1].subs(t, sqrt(y))

    Eq << algebra.le.ge.then.ge.trans.apply(Eq[1], Eq[0])

    Eq << algebra.ge_zero.then.ge_zero.sqrt.apply(Eq[-1])

    Eq << sets.ge.then.el.interval.apply(Eq[-1])

    Eq << algebra.cond.cond.then.cond.subs.apply(Eq[-1], Eq.ou, invert=True)

    Eq << Eq[-1].this.find(Greater).apply(algebra.gt.then.gt.square)

    Eq << algebra.cond.cond.then.cond.subs.apply(Eq[1], Eq[-1], invert=True)

    Eq << algebra.et.then.cond.apply(Eq[-1], 0)




if __name__ == '__main__':
    run()
# created on 2018-07-07
# updated on 2023-05-14
