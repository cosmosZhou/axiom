from util import *


@apply
def apply(is_nonpositive, le):
    x = is_nonpositive.of(Expr <= 0)
    y, S[x] = le.of(LessEqual)

    return Equal(Min(y ** 2, x ** 2), x ** 2)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True)
    Eq << apply(x <= 0, y <= x)

    Eq << Eq[-1] - x ** 2

    Eq << Eq[-1].this.lhs.apply(algebra.add.to.min)

    Eq << algebra.le_zero.le.then.le.square.apply(Eq[0], Eq[1])

    Eq << algebra.le.then.ge_zero.apply(Eq[-1])

    Eq << algebra.ge.then.eq.min.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-12-07
