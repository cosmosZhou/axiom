from util import *


@apply(simplify=False)
def apply(given, t):
    a, b = given.of(Less)

    return Less(a + t, b + t), Element(t, Interval(-oo, oo))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b = Symbol(real=True, given=True)
    t = Symbol(hyper_real=True, given=True)
    Eq << apply(a < b, t)

    Eq << sets.el.then.any.eq.apply(Eq[2])

    Eq << algebra.cond.any.then.any.et.apply(Eq[1], Eq[-1], simplify=None)
    Eq << Eq[-1].this.expr.apply(algebra.eq.cond.then.cond.subs)


if __name__ == '__main__':
    run()
# created on 2021-05-27
