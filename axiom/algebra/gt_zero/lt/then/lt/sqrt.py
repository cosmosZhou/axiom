from util import *


@apply
def apply(is_positive, lt):
    x = is_positive.of(Expr > 0)
    S[x], M = lt.of(Less)

    return Less(sqrt(x), sqrt(M))


@prove
def prove(Eq):
    from axiom import algebra

    x, M = Symbol(real=True)
    Eq << apply(x > 0, x < M)

    Eq << algebra.gt_zero.then.ge_zero.apply(Eq[0])
    Eq << algebra.ge_zero.lt.then.lt.sqrt.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-09-12
