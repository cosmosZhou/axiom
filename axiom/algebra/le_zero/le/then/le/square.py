from util import *


@apply
def apply(is_nonpositive, le):
    x = is_nonpositive.of(Expr <= 0)
    M, S[x] = le.of(LessEqual)

    return LessEqual(x * x, M * M)


@prove
def prove(Eq):
    from axiom import algebra

    x, M = Symbol(real=True)
    Eq << apply(x <= 0, M <= x)

    Eq << algebra.le.le.then.le.trans.apply(Eq[0], Eq[1])

    Eq << -Eq[-1]

    Eq << algebra.le.ge.then.ge.trans.apply(Eq[0], Eq[-1])

    Eq << algebra.le.ge.then.le_zero.apply(Eq[1], Eq[-1])

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[-1] - Eq[-1].lhs.args[1]




if __name__ == '__main__':
    run()
# created on 2019-12-07
# updated on 2023-05-20
