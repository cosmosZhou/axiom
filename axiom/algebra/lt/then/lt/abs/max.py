from util import *


@apply
def apply(given, swap=False):
    (a, b), M = given.of(Abs[Expr - Expr] < Expr)
#     |a - b| < M
    if swap:
        a, b = b, a
    return Less(abs(a), Max(abs(M + b), abs(M - b)))


@prove
def prove(Eq):
    from axiom import algebra
    M, a, b = Symbol(real=True)

    Eq << apply(Less(abs(a - b), M))

    Eq << algebra.lt.then.lt.split.abs.apply(Eq[0]) + b

    Eq << algebra.then.le.abs.apply(M + b)

    Eq << algebra.lt.le.then.lt.trans.apply(Eq[-2], Eq[-1])

    Eq << LessEqual(abs(M + b), Eq[1].rhs, plausible=True)

    Eq.strict_less_than = algebra.lt.le.then.lt.trans.apply(Eq[-2], Eq[-1])

    Eq << algebra.lt.then.lt.split.abs.apply(Eq[0], negate=True) - b

    Eq << algebra.then.le.abs.apply(M - b)

    Eq << algebra.lt.le.then.lt.trans.apply(Eq[-2], Eq[-1])

    Eq << LessEqual(abs(M - b), Eq[1].rhs, plausible=True)

    Eq << algebra.lt.le.then.lt.trans.apply(Eq[-2], Eq[-1])

    Eq << algebra.lt.lt.then.lt.abs.apply(Eq.strict_less_than, Eq[-1])


if __name__ == '__main__':
    run()

# created on 2019-12-30
