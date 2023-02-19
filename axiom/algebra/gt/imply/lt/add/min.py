from util import *


@apply
def apply(gt):
    (a, b), n = gt.of(Add > Expr)
    return Add(Min(a, n - b), Min(b, n - a)) < n


@prove
def prove(Eq):
    from axiom import algebra

    a, b, n = Symbol(real=True)
    Eq << apply(a + b > n)

    Eq <<= Eq[0] - a, Eq[0] - b

    Eq <<= algebra.gt.imply.eq.min.apply(Eq[-2]), algebra.gt.imply.eq.min.apply(Eq[-1])

    Eq << Eq[1].subs(Eq[-1], Eq[-2])

    Eq << Eq[-1] + (a + b - n)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2022-07-12
