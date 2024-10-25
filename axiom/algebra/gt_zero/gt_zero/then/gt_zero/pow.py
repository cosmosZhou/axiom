from util import *


@apply
def apply(gt_zero, given):
    n = gt_zero.of(Expr > 0)
    x = given.of(Expr > 0)
    return Greater(x ** n, 0)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True)
    n = Symbol(integer=True)
    Eq << apply(n > 0, x > 0)

    m = Symbol(integer=True, positive=True)
    Eq << algebra.gt.then.gt.pow.apply(Eq[1], m)

    Eq << algebra.cond.then.all.apply(Eq[-1], m)

    Eq << algebra.all.then.infer.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[-2].variable, n)

    Eq << algebra.gt.then.ge.strengthen.apply(Eq[0])

    Eq << algebra.cond.infer.then.cond.trans.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2023-04-15
