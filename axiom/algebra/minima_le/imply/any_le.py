from util import *


@apply
def apply(given):
    (fx, *limits), M = given.of(LessEqual[Minima])
    return Any(fx <= M, *limits)


@prove
def prove(Eq):
    from axiom import algebra

    M, a, b = Symbol(real=True, given=True)
    x = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Minima[x:a:b](f(x)) <= M)

    Eq << ~Eq[-1]

    Eq << algebra.all_gt.imply.gt_minima.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()
# created on 2019-12-01
