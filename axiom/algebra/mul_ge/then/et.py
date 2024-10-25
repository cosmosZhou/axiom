from util import *


@apply
def apply(given):
    factor, cond = given.of(GreaterEqual[Mul[Bool], 1])
    return factor >= 1, cond


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(GreaterEqual(Bool(f(x) >= 0) * y, 1))

    Eq << algebra.ge.then.gt_zero.apply(Eq[0])

    Eq << algebra.gt_zero.then.ou.split.mul.apply(Eq[-1])

    Eq << algebra.et.then.et.apply(Eq[-1])

    Eq << algebra.gt_zero.then.cond.apply(Eq[-1])

    Eq << algebra.gt.then.ge.strengthen.apply(Eq[-1])

    Eq << LessEqual(Eq[-1].lhs, 1, plausible=True)

    Eq << algebra.ge.le.then.eq.apply(Eq[-2], Eq[-1])

    Eq << Eq[0].subs(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-11-05
