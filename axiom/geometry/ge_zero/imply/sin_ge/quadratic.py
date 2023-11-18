from util import *


@apply
def apply(ge_zero):
    x = ge_zero.of(Expr >= 0)
    return sin(x) >= x * (1 - x / S.Pi)

@prove
def prove(Eq):
    from axiom import algebra, geometry, sets

    x = Symbol(real=True)
    Eq << apply(x >= 0)

    Eq << algebra.cond.given.et.infer.split.apply(Eq[1], cond=x > S.Pi)

    Eq << (x <= 0).this.apply(geometry.le_zero.imply.sin_ge.quadratic)

    Eq << Eq[-1].subs(x, S.Pi - x)

    Eq << Eq[-1].this.lhs.apply(algebra.le_zero.given.ge)

    Eq << Eq[-1].find(Mul).this.apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Add ** 2).apply(algebra.pow.to.add)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq.eq_identity = Eq[-1].this.rhs.apply(algebra.add.to.mul)

    Eq << Eq[-4].subs(Eq.eq_identity)

    Eq << Eq[-1].this.lhs.apply(algebra.ge.given.gt)

    Eq << algebra.infer.given.et.infer.split.apply(Eq[3], cond=x > S.Pi / 2)

    Eq << algebra.infer.given.et.infer.invert.apply(Eq[-1], cond=x >= 0)

    Eq << Eq[-1].this.lhs.apply(sets.le.ge.imply.el.interval)

    Eq << Eq[-1].this.lhs.apply(geometry.el_interval.imply.sin_ge.quadratic)

    Eq << Eq[-1].subs(x, S.Pi - x)

    Eq << Eq[-1].subs(Eq.eq_identity)

    Eq << Eq[-1].this.lhs.apply(sets.el.negate)

    Eq << Eq[-1].this.lhs.apply(sets.el.add, S.Pi)

    Eq << Eq[-1].this.lhs.apply(sets.el_interval.to.et)

    Eq << Eq[-1].this.find(And[~GreaterEqual]).apply(algebra.ge.given.gt)

    


if __name__ == '__main__':
    run()
# created on 2023-10-03
