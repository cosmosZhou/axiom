from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Less)

    return Less(exp(lhs), exp(rhs))


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True)
    Eq << apply(Less(x, y))

    t = Symbol(y - x)
    Eq << t.this.definition

    Eq << algebra.lt.imply.gt_zero.apply(Eq[0])

    Eq.gt_zero = algebra.eq.gt.imply.gt.subs.apply(Eq[-2], Eq[-1])

    Eq << Eq[-2] + x

    Eq << Eq[1].subs(Eq[-1].reversed)

    Eq << Eq[-1] / exp(x)

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.exp)

    r = Symbol(positive=True)
    Eq << Greater(exp(r), 1, plausible=True)

    Eq << algebra.cond.imply.all.apply(Eq[-1])

    Eq << algebra.all.imply.infer.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[-1].find(Symbol), t)

    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq.gt_zero, Eq[-1])

    


if __name__ == '__main__':
    run()
# created on 2023-04-16
