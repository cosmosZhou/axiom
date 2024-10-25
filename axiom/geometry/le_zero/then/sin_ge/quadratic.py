from util import *


@apply
def apply(le_zero):
    x = le_zero.of(Expr <= 0)
    return sin(x) >= x * (1 - x / S.Pi)

@prove
def prove(Eq):
    from axiom import geometry, algebra

    x = Symbol(real=True)
    Eq << apply(x <= 0)

    Eq << (x >= 0).this.apply(geometry.ge_zero.then.sin_le.quadratic)

    Eq << Eq[-1].subs(x, -x)

    Eq << -Eq[-1].this.lhs

    Eq << -Eq[-1].this.rhs

    Eq << algebra.cond.infer.then.cond.trans.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-10-03
